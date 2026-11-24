-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_regMax_of_injective_e20efb725643
-- name    : P2M_GroundTheory_Heights__Heights_Regular_regMax_of_injective_e20efb725643
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:51.450132+00:00
-- url     : https://prove2.me/theorems/a6e942af-8b94-4f1b-84d4-3fcc763902c4
-- title:
--   P2 M Ground Theory Heights  Heights Regular reg Max of injective e20efb725643: P2 M Ground Theory Heights  Heights Regular reg Max of injective e20efb725643
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular reg Max of injective e20efb725643 construction uses the P2 M Ground Theory Heights  Heights Regular reg Max of injective e20efb725643 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L113-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L113-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_regMax_of_injective_e20efb725643 {κ ι : Type} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (f : κ → ι) (hf : Function.Injective f) {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ)
    (hdom : ∀ i, (∀ k, f k ≠ i) → ∃ k, t i + η ≤ t (f k)) :
    regMax η t = regMax η (t ∘ f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«regMax_of_injective» := P2M_GroundTheory_Heights__Heights_Regular_regMax_of_injective_e20efb725643
