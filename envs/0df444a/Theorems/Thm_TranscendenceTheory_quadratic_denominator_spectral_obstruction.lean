-- Prove2me | Theorems.Thm_TranscendenceTheory_quadratic_denominator_spectral_obstruction
-- name    : TranscendenceTheory.quadratic_denominator_spectral_obstruction
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T23:08:39.232666+00:00
-- url     : https://prove2.me/theorems/f966e079-c401-4b0c-a739-8ebfd2c975ad
-- title:
--   Quadratic spectral restriction from an exact denominator identity
-- statement:
--   Let R be a commutative integral domain, let I be a finite index type, and let a,c:I→R. For a nonnegative integer N put
--
--   $$q_r(X)=1-a_rX+c_rX^2,\qquad
--   \Omega(X)=\prod_{r\in I}q_r(X)^N,\qquad d=2N|I|.$$
--
--   Let A∈R[X] have degree strictly less than d, and let λ∈R. If the exact polynomial identity
--
--   $$ (1-\lambda X)A(X)=\Omega(X) $$
--
--   holds, then
--
--   $$\lambda^2-a_r\lambda+c_r=0\quad\text{for some }r\in I.$$
--
--   The strict degree bound uses degree −∞ for the zero polynomial. No field structure, nonzero λ, distinct denominators or nonzero quadratic leading coefficients are assumed. If I is empty or N=0, the hypotheses are inconsistent: Ω=1 and the strict bound forces A=0. The assertion includes these cases without extra assumptions.
-- source:
--   Derived denominator-spectrum step for https://prove2.me/theorems/35428579-0ae4-47de-bc13-8f2bb94e6f52. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib Algebra/Polynomial/Reverse.lean (reflect_mul, fixed-bound coefficient reflection), BigOperators.lean (product degree bounds), Degree/Defs.lean and Eval/Defs.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. See https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Reverse.html. Reflecting a product of quadratic denominators at the uniform bound 2*N*card(I) turns an exact rational identity into a product of characteristic quadratics vanishing at the interpolation parameter. The mission connection restricts only the sufficiently long interpolation case to this finite quadratic candidate set, preserving all witnesses and bounds.

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.ComputeDegree

open Polynomial

theorem TranscendenceTheory.quadratic_denominator_spectral_obstruction
    (R ι : Type*) [CommRing R] [IsDomain R] [Fintype ι]
    (a c : ι → R) (N : ℕ) (A : Polynomial R) (z : R)
    (hA : A.degree < ((2 * N * Fintype.card ι : ℕ) : WithBot ℕ))
    (h : (1 - C z * X) * A =
      ∏ r : ι, (1 - C (a r) * X + C (c r) * X ^ 2) ^ N) :
    ∃ r : ι, z ^ 2 - a r * z + c r = 0 := by sorry
