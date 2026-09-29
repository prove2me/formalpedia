-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add
-- name    : WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/36178d2d-ea81-5440-be7d-d627e2eb8fb6
-- title:
--   Isogeny-induced endomorphisms of E(F) are closed under addition
-- statement:
--   Let $F$ be a field in a fixed universe with decidable equality, algebraically closed and of characteristic zero, and let $W$ be an affine Weierstrass curve over $F$ satisfying `W.IsElliptic`, equipped with three gate hypotheses: `GenusOnePlaceGate W`, supplying a bijection `pointEquivPlace` between $W.\mathrm{Point}$ and the places of $W.\mathrm{FunctionField}$ over $F$ (a place being a proper valuation subring containing the image of $F$ whose valuation ring is a principal ideal ring) together with the statement that every such place has degree $1$; `GenusOnePlaceGate.IsCentred W`, asserting that for each nonsingular affine point the classes of $X$ and of $Y - y$ in the coordinate ring lie in the nonunits of the valuation subring attached to that point; and `AbelTheorem W`, asserting that a divisor of degree $0$ is principal exactly when its divisor sum in $W.\mathrm{Point}$ vanishes. Let $D_1$ and $D_2$ be data of type `IsogenyEndDatum W`, each consisting of an $F$-algebra endomorphism $\iota$ of $W.\mathrm{FunctionField}$, a proof that $\iota$ is integral, and a proof that $W.\mathrm{FunctionField}$ is a finite module over itself along $\iota$; let $hN_1, hN_2$ witness `NormFormulaAlong` for them, i.e. that for every nonzero $f$ in the target and every divisor whose value at each place $w$ is $w.\mathrm{ord}(f)$, the pushforward divisor takes at each place $v$ the value $v.\mathrm{ord}(\mathrm{Norm}(f))$. Assume the induced additive endomorphisms of $W.\mathrm{Point}$ — obtained by transporting the $\mathrm{Pic}^0$ pushforward along $\iota$ through the genus-one isomorphism — have nonzero sum. Then there exist $D_3 :$ `IsogenyEndDatum W` and a norm-formula witness $hN_3$ for it whose associated endomorphism of $W.\mathrm{Point}$ equals the sum of those of $D_1$ and $D_2$.
--
--   This is the function-field model of the classical fact that the sum $\varphi + \psi = \mu \circ (\varphi \times \psi) \circ \Delta$ of two isogenies of an elliptic curve is again an isogeny unless it is the zero map, so that the endomorphisms of $E(F)$ coming from finite self-embeddings of the function field are closed under addition. It is the additive closure step used in assembling those endomorphisms into a subring of $\operatorname{End}_{\mathbb{Z}}(E(F))$, and is cited by [`WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (D₁ : IsogenyEndDatum W) (hN₁ : NormFormulaAlong F D₁.ι D₁.hfin)
    (D₂ : IsogenyEndDatum W) (hN₂ : NormFormulaAlong F D₂.ι D₂.hfin)
    (h : D₁.pointEnd hN₁ + D₂.pointEnd hN₂ ≠ 0) :
    ∃ (D₃ : IsogenyEndDatum W) (hN₃ : NormFormulaAlong F D₃.ι D₃.hfin),
      D₃.pointEnd hN₃ = D₁.pointEnd hN₁ + D₂.pointEnd hN₂ := by sorry
