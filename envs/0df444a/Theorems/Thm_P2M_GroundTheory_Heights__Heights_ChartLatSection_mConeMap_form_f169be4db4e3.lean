-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_mConeMap_form_f169be4db4e3
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatSection_mConeMap_form_f169be4db4e3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:56.950872+00:00
-- url     : https://prove2.me/theorems/96824c5d-0937-4c6b-bf3d-5087b8ebd9ed
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Section m Cone Map form f169be4db4e3: P2 M Ground Theory Heights  Heights Chart Lat Section m Cone Map form f169be4db4e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Section m Cone Map form f169be4db4e3 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Section m Cone Map form f169be4db4e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L15-L33

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatSection_mConeMap_form_f169be4db4e3 (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    Geo.mConeMap (ι := blockIdx n) y f = C (aeval y f) * ∏ k, (X k : MvPolynomial ι Ω) ^ δ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatSection».«mConeMap_form» := P2M_GroundTheory_Heights__Heights_ChartLatSection_mConeMap_form_f169be4db4e3
