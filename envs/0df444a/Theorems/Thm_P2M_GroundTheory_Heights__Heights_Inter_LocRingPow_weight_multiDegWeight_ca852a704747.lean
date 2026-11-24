-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_weight_multiDegWeight_ca852a704747
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_weight_multiDegWeight_ca852a704747
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:07.200605+00:00
-- url     : https://prove2.me/theorems/76426dd5-5fa8-4c2f-ab40-e8c644b0fa05
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Pow weight multi Deg Weight ca852a704747: P2 M Ground Theory Heights  Heights Inter Loc Ring Pow weight multi Deg Weight ca852a704747
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Pow weight multi Deg Weight ca852a704747 construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Pow weight multi Deg Weight ca852a704747 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L21-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.LocRingPow
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_weight_multiDegWeight_ca852a704747 (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (multiDegWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingPow».«weight_multiDegWeight» := P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_weight_multiDegWeight_ca852a704747
