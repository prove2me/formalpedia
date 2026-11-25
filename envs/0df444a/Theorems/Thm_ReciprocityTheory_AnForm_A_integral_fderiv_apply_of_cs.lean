-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integral_fderiv_apply_of_cs
-- name    : ReciprocityTheory.AnForm.A.integral_fderiv_apply_of_cs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:05:59.060124+00:00
-- url     : https://prove2.me/theorems/b59c6bf1-b2ed-4485-b3c2-533e4137bad4
-- title:
--   A: integral fderiv apply of cs
-- statement:
--   The A construction uses the integral fderiv apply of cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L18-L26

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

theorem ReciprocityTheory.AnForm.A.integral_fderiv_apply_of_cs {D : ℕ} {g : (Fin D → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) (u : Fin D → ℂ) : ∫ z, fderiv ℝ g z u = 0 := by sorry
