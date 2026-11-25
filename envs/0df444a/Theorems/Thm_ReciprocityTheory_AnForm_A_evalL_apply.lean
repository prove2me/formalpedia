-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_evalL_apply
-- name    : ReciprocityTheory.AnForm.A.evalL_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:54.123933+00:00
-- url     : https://prove2.me/theorems/8a42bb35-c6f7-47a5-bfda-5c60dc5ad8f2
-- title:
--   A: eval L apply
-- statement:
--   The A construction uses the eval L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L97-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L97-L97

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

theorem ReciprocityTheory.AnForm.A.evalL_apply {D : ℕ} (x w : Fin D → ℂ) (H : BilinSp D) : evalL x w H = H x w := by sorry
