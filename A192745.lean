import Mathlib

namespace A192745

-- The coefficient pair of the polynomial P_n after X^2 = X + 1.
-- P_0 = 1 and P_(n+1) = X * P_n + (n+1)!.
def pair : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 =>
      let v := pair n
      (v.2 + (Nat.factorial (n + 1) : Int), v.1 + v.2)

def a (n : Nat) : Int := (pair n).2

private theorem pair_succ (n : Nat) :
    pair (n + 1) =
      ((pair n).2 + (Nat.factorial (n + 1) : Int),
       (pair n).1 + (pair n).2) := by
  simp [pair]

-- This is the inhomogeneous Fibonacci recurrence for the linear coefficient.
theorem fibonacci_factorial_step (n : Nat) :
    a (n + 2) = a (n + 1) + a n + (Nat.factorial (n + 1) : Int) := by
  simp only [a]
  rw [pair_succ (n + 1), pair_succ n]
  simp only [Prod.snd, Prod.fst]
  ring

-- Eliminating the factorial from two successive instances gives Mathar's
-- homogeneous recurrence.  The indexing n+3 corresponds to OEIS n >= 3.
theorem mathar_recurrence (n : Nat) :
    a (n + 3) - (n + 3 : Int) * a (n + 2) +
      (n + 1 : Int) * a (n + 1) + (n + 2 : Int) * a n = 0 := by
  have h1 := fibonacci_factorial_step n
  have h2 := fibonacci_factorial_step (n + 1)
  have hf : (Nat.factorial (n + 2) : Int) =
      (n + 2 : Int) * (Nat.factorial (n + 1) : Int) := by
    have heq : n + 2 = (n + 1) + 1 := by omega
    rw [heq, Nat.factorial_succ]
    push_cast
    ring
  linear_combination h2 - (n + 2 : Int) * h1 + hf

-- A simple algebraic characterization of the polynomial reduction:
-- every element with x^2 = x+1 evaluates P_n as its reduced coefficient pair.
-- This identifies the pair with the canonical remainder by uniqueness of
-- degree < 2 representatives, a step not formalized via modByMonic here.
noncomputable def P : Nat → Polynomial Int
  | 0 => 1
  | n + 1 => Polynomial.X * P n + Polynomial.C (Nat.factorial (n + 1) : Int)

theorem polynomial_evaluation {R : Type*} [CommRing R]
    (x : R) (hx : x ^ 2 = x + 1) (n : Nat) :
    (P n).eval₂ (Int.castRingHom R) x =
      ((pair n).1 : R) + ((pair n).2 : R) * x := by
  induction n with
  | zero => simp [P, pair]
  | succ n ih =>
      rw [P]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [ih, pair_succ]
      simp only [Prod.fst, Prod.snd]
      push_cast
      simp only [map_natCast]
      linear_combination ((pair n).2 : R) * hx

#print axioms fibonacci_factorial_step
#print axioms mathar_recurrence
#print axioms polynomial_evaluation

end A192745
