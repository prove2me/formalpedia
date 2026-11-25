-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_comb
-- name    : ReciprocityTheory.AnForm.A.mdisc_update_comb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:49.148672+00:00
-- url     : https://prove2.me/theorems/12e6aa55-3c32-4514-8c64-ae86f9bd0a65
-- title:
--   A: mdisc update comb
-- statement:
--   The A construction uses the mdisc update comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L206-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L206-L210

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

theorem ReciprocityTheory.AnForm.A.mdisc_update_comb {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (q : Fin D) (c d : ℂ)
    (B C : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A q (c • B + d • C)) =
      c * mdisc (Function.update A q B) + d * mdisc (Function.update A q C) := by sorry
