-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_expand
-- name    : ReciprocityTheory.AnForm.A.mdisc_update_expand
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:42.419202+00:00
-- url     : https://prove2.me/theorems/18e398f1-a481-44e6-8d77-d9fbae231c33
-- title:
--   A: mdisc update expand
-- statement:
--   The A construction uses the mdisc update expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L212-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L212-L229

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

theorem ReciprocityTheory.AnForm.A.mdisc_update_expand {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (q : Fin D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A q X) =
      ∑ a, ∑ b, X a b * mdisc (Function.update A q (Matrix.single a b 1)) := by sorry
