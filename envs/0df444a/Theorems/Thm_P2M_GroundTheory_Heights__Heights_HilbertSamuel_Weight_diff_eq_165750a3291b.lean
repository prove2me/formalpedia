-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_diff_eq_165750a3291b
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_diff_eq_165750a3291b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:15:57.307133+00:00
-- url     : https://prove2.me/theorems/6dcdb77b-b105-5909-8def-868e6877a541
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Weight diff eq 165750a3291b: P2 M Ground Theory Heights  Heights Hilbert Samuel Weight diff eq 165750a3291b
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Weight diff eq 165750a3291b construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Weight diff eq 165750a3291b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanObjects.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanObjects.lean#L68-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
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
open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X]
open GroundTheory.Heights₂.Heights.HilbertSamuel.Weight
variable {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_diff_eq_165750a3291b (W₁ W₀ : Weight L) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    diff W₁ W₀ x = W₁.φ j x - W₀.φ j x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«Weight».«diff_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_diff_eq_165750a3291b
