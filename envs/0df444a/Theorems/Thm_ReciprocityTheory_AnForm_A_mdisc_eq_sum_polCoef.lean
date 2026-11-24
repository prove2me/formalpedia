-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_polCoef
-- name    : ReciprocityTheory.AnForm.A.mdisc_eq_sum_polCoef
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:42.874278+00:00
-- url     : https://prove2.me/theorems/6b36e290-7657-4fd9-872c-725b0e839209
-- title:
--   A: mdisc eq sum pol Coef
-- statement:
--   The A construction uses the mdisc eq sum pol Coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean#L71-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section

theorem ReciprocityTheory.AnForm.A.mdisc_eq_sum_polCoef {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc A = (1 / (D.factorial : ℂ)) *
      ∑ r : Fin D → Fin D, polCoef r * (Matrix.of fun i => A (r i) i).det := by sorry
