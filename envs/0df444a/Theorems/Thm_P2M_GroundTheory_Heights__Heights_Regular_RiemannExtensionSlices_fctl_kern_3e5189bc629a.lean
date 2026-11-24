-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_fctl_kern_3e5189bc629a
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_fctl_kern_3e5189bc629a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:31.085504+00:00
-- url     : https://prove2.me/theorems/1dc40c1d-e58d-4778-96c7-598a67ad0c81
-- title:
--   P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices fctl kern 3e5189bc629a: P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices fctl kern 3e5189bc629a
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices fctl kern 3e5189bc629a construction uses the P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices fctl kern 3e5189bc629a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L175-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L175-L181

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_fctl_kern_3e5189bc629a {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (f : (Fin n → ℂ) → ℂ)
    (hz : z ∈ ball c r) :
    fctl c r f (kern c r z) = ∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RiemannExtensionSlices».«fctl_kern» := P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_fctl_kern_3e5189bc629a
