-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_eq_zero_of_mem_a3afea90a62b
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_eq_zero_of_mem_a3afea90a62b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:23.054796+00:00
-- url     : https://prove2.me/theorems/3bb0f954-3898-5e89-90ea-827666c562f5
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Section aeval eq zero of mem a3afea90a62b: P2 M Ground Theory Heights  Heights Chart Lat Section aeval eq zero of mem a3afea90a62b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Section aeval eq zero of mem a3afea90a62b construction uses the P2 M Ground Theory Heights  Heights Chart Lat Section aeval eq zero of mem a3afea90a62b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L49-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_eq_zero_of_mem_a3afea90a62b (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ}
    (hf : f ∈ Geo.mCoordIdeal (ι := blockIdx n) y) : aeval y f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatSection».«aeval_eq_zero_of_mem» := P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_eq_zero_of_mem_a3afea90a62b
