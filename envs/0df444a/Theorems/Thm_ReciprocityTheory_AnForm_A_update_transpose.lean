-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_update_transpose
-- name    : ReciprocityTheory.AnForm.A.update_transpose
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:38.650055+00:00
-- url     : https://prove2.me/theorems/1125ee73-f7d3-5270-8194-537e16374ba9
-- title:
--   A: update transpose
-- statement:
--   The A construction uses the update transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L246-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L246-L252

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

theorem ReciprocityTheory.AnForm.A.update_transpose {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    (fun r => (Function.update (Function.update A p X) q Y r)ᵀ) =
      Function.update (Function.update (fun r => (A r)ᵀ) p Xᵀ) q Yᵀ := by sorry
