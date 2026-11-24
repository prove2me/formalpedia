-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_add_of_dimOne_cd9bf8d25634
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_add_of_dimOne_cd9bf8d25634
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:59.410895+00:00
-- url     : https://prove2.me/theorems/7f867b02-f6c8-4f61-9266-87ecebed55ec
-- title:
--   P2 M Ground Theory Heights  Heights Inter pts Integral add of dim One cd9bf8d25634: P2 M Ground Theory Heights  Heights Inter pts Integral add of dim One cd9bf8d25634
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pts Integral add of dim One cd9bf8d25634 construction uses the P2 M Ground Theory Heights  Heights Inter pts Integral add of dim One cd9bf8d25634 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L142-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L142-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_add_of_dimOne_cd9bf8d25634 (hFF : FibreFiniteStatement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {g g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ z ∈ mcPts P, g z = g₁ z + g₂ z) :
    ptsIntegral P φ g = ptsIntegral P φ g₁ + ptsIntegral P φ g₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ptsIntegral_add_of_dimOne» := P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_add_of_dimOne_cd9bf8d25634
