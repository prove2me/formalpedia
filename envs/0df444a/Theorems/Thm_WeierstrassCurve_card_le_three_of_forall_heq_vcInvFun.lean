-- Prove2me | Theorems.Thm_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun
-- name    : WeierstrassCurve.card_le_three_of_forall_heq_vcInvFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/c3428d7b-d5cb-516c-88bd-e270b3c47398
-- title:
--   A model automorphism ≠ ± 1 fixes at most three points
-- statement:
--   Let $K$ be a field, let $E$ be a Weierstrass curve over $K$ given by coefficients $a_1,a_2,a_3,a_4,a_6$, and let $\beta=(u;r,s,t)$ be an admissible change of variables over $K$, with $u \in K^\times$. Assume that $\beta$ fixes the model, $\beta \cdot E = E$, that $\beta$ is not the identity change of variables, and that $\beta$ is not the change of variables $(-1;0,-a_1,-a_3)$. Let $F$ be a finite set of points of the affine curve attached to $E$ (that is, of the pointed set consisting of the point at infinity together with the nonsingular $K$-points of the affine Weierstrass equation), and suppose that every $P \in F$ is fixed by the transport of points along $\beta$ in the sense that `Point.vcInvFun β E.toAffine P` is heterogeneously equal to $P$; here `vcInvFun` sends the point at infinity to the point at infinity and an affine point $(x,y)$ to the point with coordinates $\bigl(u^{-2}(x-r),\; u^{-3}(y-t-s(x-r))\bigr)$ on the transformed curve $\beta \cdot E$, which by hypothesis is $E$ again. Then $F$ has at most $3$ elements.
--
--   This is the rigidity statement that an automorphism of a Weierstrass model other than the identity and the negation $(-1;0,-a_1,-a_3)$ has at most three fixed points, the classical bound $\#\ker(1-\beta) = \deg(1-\beta) \le 3$ in elementary, characteristic-free form for arbitrary Weierstrass cubics. It is used to compute that the stabiliser occurring in [`WeierstrassCurve.natCard_stabilizer_torsionOrbit_bot_eq_two`](thm.html#WeierstrassCurve.natCard_stabilizer_torsionOrbit_bot_eq_two) has order two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.card_le_three_of_forall_heq_vcInvFun
    {K : Type*} [Field K] [DecidableEq K] (E : WeierstrassCurve K)
    (β : WeierstrassCurve.VariableChange K) (hβ : β • E = E) (h1 : β ≠ 1)
    (hneg : β ≠ ⟨-1, 0, -E.a₁, -E.a₃⟩)
    (F : Finset E.toAffine.Point) (hF : ∀ P ∈ F, HEq (Point.vcInvFun β E.toAffine P) P) :
    F.card ≤ 3 := by sorry
