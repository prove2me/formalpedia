-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_fderiv_apply_of_cs
-- name    : ReciprocityTheory.AnForm.A.integrable_fderiv_apply_of_cs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:29.228457+00:00
-- url     : https://prove2.me/theorems/e045c677-c558-4301-9b54-cda7a7a3ea27
-- title:
--   A: integrable fderiv apply of cs
-- statement:
--   The A construction uses the integrable fderiv apply of cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L11-L16

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.A.integrable_fderiv_apply_of_cs {D : ℕ} {g : (Fin D → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) (u : Fin D → ℂ) : Integrable (fun z => fderiv ℝ g z u) := by sorry
