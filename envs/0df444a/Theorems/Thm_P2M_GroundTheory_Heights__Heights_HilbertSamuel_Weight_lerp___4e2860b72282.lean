-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_lerp___4e2860b72282
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_lerp___4e2860b72282
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:15:51.393707+00:00
-- url     : https://prove2.me/theorems/0ee18716-94b6-4db1-a8ec-44805a9d76d4
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Weight lerp   4e2860b72282: P2 M Ground Theory Heights  Heights Hilbert Samuel Weight lerp   4e2860b72282
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Weight lerp   4e2860b72282 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Weight lerp   4e2860b72282 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/HolLineBundleToAltTransition.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/HolLineBundleToAltTransition.lean#L68-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_SectionL2NormSq
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HolLineBundleToAltTransition
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
open scoped ComplexConjugate ENNReal ContDiff
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
open GroundTheory.Heights₂.Heights.HilbertSamuel.Weight
variable {L : HolLineBundle A}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_lerp___4e2860b72282 (W₀ W₁ : Weight L) (t : ℝ) :
    (W₀.lerp W₁ t).φ = IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.interp W₀.φ W₁.φ t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«Weight».«lerp_φ» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_lerp___4e2860b72282
