-- Prove2me | Theorems.Thm_PI_GTNum_abs_cBr_le
-- name    : PI.GTNum.abs_cBr_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:33:38.910182+00:00
-- url     : https://prove2.me/theorems/1d9c4042-dba8-5998-96d6-2e0889054971
-- title:
--   GTNum: abs c Br le
-- statement:
--   The GTNum construction uses the abs c Br le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/GTCoefTopMain.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/GTCoefTopMain.lean#L12-L33

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

theorem PI.GTNum.abs_cBr_le {n N : ℕ} (h : n + 1 = N) (hn : 0 < n) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace h lam sg) :
    |cBr h lam sg| ≤ (2 * (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) + (N : ℤ)) ^
      (n * ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card) := by sorry
