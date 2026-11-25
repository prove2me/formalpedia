-- Prove2me | Theorems.Thm_PI_GTNum_card_R_erase
-- name    : PI.GTNum.card_R_erase
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:31:02.6338+00:00
-- url     : https://prove2.me/theorems/2e5166b7-4713-456d-9af6-08d4a45e48e3
-- title:
--   GTNum: card R erase
-- statement:
--   The GTNum construction uses the card R erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L67-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
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
variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)

theorem PI.GTNum.card_R_erase (hI : Interlace h lam sg) (i : Fin n) :
    ((((Rset h lam sg i).erase (sg.w i)).card : ℕ) : ℤ) =
      min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg) := by sorry
