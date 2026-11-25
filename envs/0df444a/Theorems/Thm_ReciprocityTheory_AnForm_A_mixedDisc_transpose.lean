-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDisc_transpose
-- name    : ReciprocityTheory.AnForm.A.mixedDisc_transpose
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:36.182241+00:00
-- url     : https://prove2.me/theorems/7f4503c7-e6f8-46e5-b808-062378498b68
-- title:
--   A: mixed Disc transpose
-- statement:
--   The A construction uses the mixed Disc transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L42-L47

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

theorem ReciprocityTheory.AnForm.A.mixedDisc_transpose {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => (A k)ᵀ) = mdisc A := by sorry
