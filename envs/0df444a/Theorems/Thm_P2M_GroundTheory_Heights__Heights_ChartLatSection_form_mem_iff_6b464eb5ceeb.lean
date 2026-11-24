-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_form_mem_iff_6b464eb5ceeb
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatSection_form_mem_iff_6b464eb5ceeb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:38.603997+00:00
-- url     : https://prove2.me/theorems/0a3cf6ec-55ed-4d2e-b3b1-2420ab758489
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Section form mem iff 6b464eb5ceeb: P2 M Ground Theory Heights  Heights Chart Lat Section form mem iff 6b464eb5ceeb
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Section form mem iff 6b464eb5ceeb construction uses the P2 M Ground Theory Heights  Heights Chart Lat Section form mem iff 6b464eb5ceeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L35-L45

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatSection_form_mem_iff_6b464eb5ceeb (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatSection».«form_mem_iff» := P2M_GroundTheory_Heights__Heights_ChartLatSection_form_mem_iff_6b464eb5ceeb
