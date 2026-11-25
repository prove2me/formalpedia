-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuousOn_source_of_chart_59202810ddfe
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuousOn_source_of_chart_59202810ddfe
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:57.893064+00:00
-- url     : https://prove2.me/theorems/2b4f318f-ea5e-502c-981c-162271619f9c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel continuous On source of chart 59202810ddfe: P2 M Ground Theory Heights  Heights Hilbert Samuel continuous On source of chart 59202810ddfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel continuous On source of chart 59202810ddfe construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel continuous On source of chart 59202810ddfe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuousOn_source_of_chart_59202810ddfe {E : Type*} [TopologicalSpace E] {f : X → E} (j : Fin A.n)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source)) :
    ContinuousOn f (A.chart j).source := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«continuousOn_source_of_chart» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuousOn_source_of_chart_59202810ddfe
