-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_encard_iUnion_nat_eq_tsum_46bad95e9c62
-- name    : P2M_GroundTheory_Heights__Heights_encard_iUnion_nat_eq_tsum_46bad95e9c62
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:47.21062+00:00
-- url     : https://prove2.me/theorems/cac6029d-b919-443e-a482-3a977b56adb7
-- title:
--   P2 M Ground Theory Heights  Heights encard i Union nat eq tsum 46bad95e9c62: P2 M Ground Theory Heights  Heights encard i Union nat eq tsum 46bad95e9c62
-- statement:
--   The P2 M Ground Theory Heights  Heights encard i Union nat eq tsum 46bad95e9c62 construction uses the P2 M Ground Theory Heights  Heights encard i Union nat eq tsum 46bad95e9c62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaMultiplicity.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaMultiplicity.lean#L25-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module Set Filter Function
open scoped ENNReal NNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_encard_iUnion_nat_eq_tsum_46bad95e9c62 {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Disjoint on s)) :
    (((⋃ n, s n).encard : ℕ∞) : ℝ≥0∞) = ∑' n, (((s n).encard : ℕ∞) : ℝ≥0∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«encard_iUnion_nat_eq_tsum» := P2M_GroundTheory_Heights__Heights_encard_iUnion_nat_eq_tsum_46bad95e9c62
