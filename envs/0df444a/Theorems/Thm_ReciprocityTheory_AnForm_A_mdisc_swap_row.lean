-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_swap_row
-- name    : ReciprocityTheory.AnForm.A.mdisc_swap_row
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:42.995883+00:00
-- url     : https://prove2.me/theorems/4b35081a-18be-46fc-b401-66245ab71559
-- title:
--   A: mdisc swap row
-- statement:
--   The A construction uses the mdisc swap row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L49-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean#L49-L90

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

theorem ReciprocityTheory.AnForm.A.mdisc_swap_row {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (j k a b : Fin D) :
    mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (Matrix.single a b 1)) =
      - mdisc (Function.update (Function.update A p (Matrix.single a k 1)) q
          (Matrix.single j b 1)) := by sorry
