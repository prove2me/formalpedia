-- Prove2me | Theorems.Thm_WeierstrassCurve_Phi_PsiSq_no_common_eval_zero_even
-- name    : WeierstrassCurve.Phi_PsiSq_no_common_eval_zero_even
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:46.607013+00:00
-- url     : https://prove2.me/theorems/a27807e2-19f4-4ca2-84cc-71b6c367cc87
-- title:
--   Even-index numerator and denominator have no common zero
-- statement:
--   Let $k$ be a field, let $W/k$ be an elliptic Weierstrass curve, assume $4≠0$, and let $x∈k$ and $m∈ℤ$. Then the even-index x-coordinate numerator and squared denominator do not vanish simultaneously: $$¬(Φ_{2m}(x)=0 ∧ ΨSq_{2m}(x)=0).$$ This guarantees that the even-index division-polynomial pair defines a projective x-coordinate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneCoprimality
import Definitions.Def_WardSomos

open Polynomial
open scoped Polynomial
open FLT.EDS
open WeierstrassCurve
variable {k : Type*} [Field k]

theorem WeierstrassCurve.Phi_PsiSq_no_common_eval_zero_even
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0) (m : ℤ) :
    ¬ ((W.Φ (2 * m)).eval x = 0 ∧ (W.ΨSq (2 * m)).eval x = 0) := by sorry
