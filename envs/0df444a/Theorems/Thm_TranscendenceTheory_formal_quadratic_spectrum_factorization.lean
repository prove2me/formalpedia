-- Prove2me | Theorems.Thm_TranscendenceTheory_formal_quadratic_spectrum_factorization
-- name    : TranscendenceTheory.formal_quadratic_spectrum_factorization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T23:32:36.671198+00:00
-- url     : https://prove2.me/theorems/b65cfd3e-eb42-49cc-ba14-2327a768e094
-- title:
--   Formal quadratic spectra as two branch values
-- statement:
--   Let R be a commutative ring, S a commutative integral domain, f:R→S a unital ring homomorphism, and A,B,D,Y formal power series over R satisfying Y²=D. For every z∈S,
--
--   $$z^2-f([X^0](2A))z+f([X^0](A^2-DB^2))=0$$
--
--   if and only if
--
--   $$z=f([X^0](A+YB))\quad\text{or}\quad z=f([X^0](A-YB)).$$
--
--   No division, injectivity of f, nonzero discriminant, or distinctness of the two values is assumed. The equivalence includes characteristic two and Y with zero constant coefficient.
-- source:
--   Derived explicit-spectrum step for https://prove2.me/theorems/cd37a9c4-c5e4-4d5a-ac05-c14cf6061cfa. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib RingTheory/PowerSeries/Basic.lean (constantCoeff), Derivative.lean (coeff_derivative), Algebra/MvPolynomial/Eval.lean (comp_aeval_apply), and RingTheory/Ideal/Span.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. See https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MvPolynomial/Eval.html and https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/PowerSeries/Basic.html. The connection reuses the Proved affine-coordinate evaluation theorem https://prove2.me/theorems/97b777a3-60dc-430c-bd7d-92dddbcb3e7e. The energy identity factors each characteristic quadratic. Its roots are the original polynomial values at the chart point and at its reflection in coordinate 2 only. All other coordinates and all frontier witnesses and bounds are preserved.

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

theorem TranscendenceTheory.formal_quadratic_spectrum_factorization
    (R S : Type*) [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S)
    (A B D Y : PowerSeries R) (hY : Y ^ 2 = D) (z : S) :
    z ^ 2 - f (PowerSeries.coeff 0 (2 * A)) * z +
        f (PowerSeries.coeff 0 (A ^ 2 - D * B ^ 2)) = 0 ↔
      z = f (PowerSeries.coeff 0 (A + Y * B)) ∨
        z = f (PowerSeries.coeff 0 (A - Y * B)) := by sorry
