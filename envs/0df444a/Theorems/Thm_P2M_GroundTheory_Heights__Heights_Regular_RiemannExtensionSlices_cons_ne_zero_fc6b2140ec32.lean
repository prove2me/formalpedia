-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_ne_zero_fc6b2140ec32
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_ne_zero_fc6b2140ec32
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:36.380832+00:00
-- url     : https://prove2.me/theorems/cdc1dca4-4f83-442f-ac23-0063f721076c
-- title:
--   P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cons ne zero fc6b2140ec32: P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cons ne zero fc6b2140ec32
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cons ne zero fc6b2140ec32 construction uses the P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cons ne zero fc6b2140ec32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L39-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
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
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices

theorem P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_ne_zero_fc6b2140ec32 {n : ℕ} {x : ℂ} (hx : x ≠ 0) {y : Fin n → ℂ} (hy : ∀ i, y i ≠ 0) :
    ∀ i, (Fin.cons x y : Fin (n + 1) → ℂ) i ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RiemannExtensionSlices».«cons_ne_zero» := P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_ne_zero_fc6b2140ec32
