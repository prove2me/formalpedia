-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add
-- name    : WeierstrassCurve.Affine.IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/f8a39c1e-1459-50cb-893b-11563e5e5727
-- title:
--   Pointwise sum of two isogeny end data is realised
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero (with decidable equality) and let $W$ be an affine Weierstrass curve over $F$ that is elliptic. Assume the place gate data `GenusOnePlaceGate W`: a bijection `pointEquivPlace` between the group $W(F)$ of points `W.Point` and the places of $F$ in the function field `W.FunctionField`, all of whose places have degree $1$, with `placeOfPoint` denoting this bijection; assume it is centred, i.e. for each nonsingular pair $(x,y)$ the images in the function field of the coordinate classes `XClass W x` and `YClass W (C y)` lie in the nonunits of the valuation subring of the place attached to `Point.some x y h`; and assume `AbelTheorem W`, i.e. a divisor of degree $0$ is principal exactly when its sum of points `divisorSum` vanishes. Let $D_1, D_2$ be isogeny end data: each consists of an $F$-algebra endomorphism $\iota$ of `W.FunctionField` whose underlying ring map is integral, together with the finiteness of `W.FunctionField` as a module over itself along $\iota$. Assume further norm formulae $hN_1, hN_2$, i.e. the divisor push-forward norm formula `NormFormulaAlong F Dᵢ.ι Dᵢ.hfin` for each, and that the sum `D₁.pointEnd hN₁ + D₂.pointEnd hN₂` of the two induced additive endomorphisms of `W.Point` (obtained by push-forward transport) is nonzero. Then there exists an isogeny end datum $D_3$ on $W$ such that for every point $P$ of $W$, the place obtained by pulling back `placeOfPoint P` along $D_3.\iota$ is the place of the point $Q_1 + Q_2$, where $Q_i$ is the point corresponding under `pointEquivPlace` to the pullback of `placeOfPoint P` along $D_i.\iota$. Note that $D_3$ is produced without an accompanying norm formula, and the assertion is the pointwise identity of places, not an identity of induced endomorphisms.
--
--   This is the closure under pointwise addition of the set of maps $E \to E$ realised by finite $F$-algebra self-embeddings of the function field, in the place-theoretic formulation of the curves–fields correspondence: the new embedding is given by chord-and-tangent addition of the two generic points, and the content is that the compatibility with places holds at every point, including those where the addition formulae degenerate. It is used by [`WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_add`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_add), which upgrades it to the statement that the sum of the two induced endomorphisms of $W(F)$ is again induced by an isogeny end datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (D₁ : IsogenyEndDatum W) (hN₁ : NormFormulaAlong F D₁.ι D₁.hfin)
    (D₂ : IsogenyEndDatum W) (hN₂ : NormFormulaAlong F D₂.ι D₂.hfin)
    (h : D₁.pointEnd hN₁ + D₂.pointEnd hN₂ ≠ 0) :
    ∃ D₃ : IsogenyEndDatum W, ∀ P : W.Point,
      (placeOfPoint P).restrictAlong D₃.ι D₃.hι
        = placeOfPoint
            ((pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D₁.ι D₁.hι)
              + (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D₂.ι D₂.hι)) := by sorry
