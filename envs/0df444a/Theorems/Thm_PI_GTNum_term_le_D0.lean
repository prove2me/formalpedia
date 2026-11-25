-- Prove2me | Theorems.Thm_PI_GTNum_term_le_D0
-- name    : PI.GTNum.term_le_D0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:55.166612+00:00
-- url     : https://prove2.me/theorems/354d503e-e76b-4336-a4ff-77ad154936dc
-- title:
--   GTNum: term le D0
-- statement:
--   The GTNum construction uses the term le D0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L26-L29

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

theorem PI.GTNum.term_le_D0 (hI : Interlace h lam sg) (i : Fin n) :
    sg.w i - lam.w ⟨i.1 + 1, by omega⟩ ≤ D0 h lam sg := by sorry
