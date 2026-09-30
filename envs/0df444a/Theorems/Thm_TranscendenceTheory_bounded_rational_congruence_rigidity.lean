-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_rational_congruence_rigidity
-- name    : TranscendenceTheory.bounded_rational_congruence_rigidity
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T22:48:56.018461+00:00
-- url     : https://prove2.me/theorems/98229524-48de-4835-add1-3d00eba51b51
-- title:
--   Exactness of sufficiently long rational congruences
-- statement:
--   Let R be any commutative ring. Let Q,A∈R[X], let α,λ∈R, and let d,s be nonnegative integers such that
--
--   $$\deg Q\le d,\qquad \deg A<d,\qquad d\le s.$$
--
--   Then
--
--   $$X^{s+1}\mid (1-\lambda X)A-\alpha Q
--   \quad\Longleftrightarrow\quad
--   (1-\lambda X)A=\alpha Q.$$
--
--   Both statements are in R[X]. Thus a sufficiently long congruence between these bounded-degree expressions is already an exact polynomial identity.
--
--   In the strict bound on A, the zero polynomial has degree −∞, so A=0 is permitted even when d=0. Lean expresses the bound on Q using natural degree, which assigns zero to the zero polynomial and is equivalent to the stated upper bound because d≥0. There is no field, integral-domain, inverse or nonvanishing assumption.
-- source:
--   Derived interpolation-rigidity step for https://prove2.me/theorems/c334622d-2651-4fed-ae97-42d3ef348d2a. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib Algebra/Polynomial/Div.lean (X_pow_dvd_iff), Degree/Defs.lean and Degree/Operations.lean (degree inequalities and coefficient vanishing), and Eval/Degree.lean (degree bounds under coefficient maps), revision 0df444a360eaa60ab8c11dca51a86af692955474. See https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Degree/Operations.html and https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Div.html. The polynomial (1-z*X)*A-alpha*Q has degree at most d when deg(A)<d and deg(Q)<=d. Divisibility by X^(s+1) for s>=d therefore makes it zero. The mission connection proves the degree bound for weighted numerators after scalar extension, and uses an exact case split at d=2*N*card(Z), preserving all witnesses and bounds.

import Mathlib.Algebra.Polynomial.Div

open Polynomial

theorem TranscendenceTheory.bounded_rational_congruence_rigidity
    (R : Type*) [CommRing R] (Q A : Polynomial R) (α z : R) (d s : ℕ)
    (hQ : Q.natDegree ≤ d) (hA : A.degree < (d : WithBot ℕ)) (hds : d ≤ s) :
    X ^ (s + 1) ∣ (1 - C z * X) * A - C α * Q ↔
      (1 - C z * X) * A = C α * Q := by sorry
