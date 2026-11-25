-- Prove2me | Theorems.Thm_PI_GTNum_top_indep
-- name    : PI.GTNum.top_indep
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:58:20.381622+00:00
-- url     : https://prove2.me/theorems/4bf18256-4100-40cf-b0c2-6c4ec8ccf8a2
-- title:
--   GTNum: top indep
-- statement:
--   The GTNum construction uses the top indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/GTCoefTopMain.lean#L35-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/GTCoefTopMain.lean#L35-L69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTCoefTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_GTCoefTopMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTNum
open Formalism.BasicNotions PI Finset

theorem PI.GTNum.top_indep {n N : ℕ} (h : n + 1 = N) (hn : 0 < n) (lam lam' : DomWeight N) (sg : DomWeight n)
    (hag : ∀ i : Fin N, i.1 ≠ 0 → lam'.w i = lam.w i)
    (htop : lam.w ⟨1, by omega⟩ + D0 h lam sg ≤ lam.w ⟨0, by omega⟩)
    (htop' : lam'.w ⟨1, by omega⟩ + D0 h lam' sg ≤ lam'.w ⟨0, by omega⟩) :
    cBr h lam' sg = cBr h lam sg ∧ D1 h lam' sg = D1 h lam sg := by sorry
