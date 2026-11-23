-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_differentiableAt_snd_fderiv
-- name    : ReciprocityTheory.AnForm.A.differentiableAt_snd_fderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:58.758764+00:00
-- url     : https://prove2.me/theorems/aa1242f7-4247-4d47-8782-9fd915898c0a
-- title:
--   A: differentiable At snd fderiv
-- statement:
--   The A construction uses the differentiable At snd fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L15-L19

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.A.differentiableAt_snd_fderiv {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : ContDiffAt ℝ 3 φ z) : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ φ)) z := by sorry
