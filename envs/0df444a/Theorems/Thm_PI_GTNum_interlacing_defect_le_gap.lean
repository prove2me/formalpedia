-- Prove2me | Theorems.Thm_PI_GTNum_interlacing_defect_le_gap
-- name    : PI.GTNum.interlacing_defect_le_gap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:31:27.96858+00:00
-- url     : https://prove2.me/theorems/9444ff58-0ade-4ff8-8b41-905160711292
-- title:
--   GTNum: interlacing defect le gap
-- statement:
--   The GTNum construction uses the interlacing defect le gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L34-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L34-L55

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

theorem PI.GTNum.interlacing_defect_le_gap (hI : Interlace h lam sg) (hn : 0 < n) :
    D0 h lam sg ≤ sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩ := by sorry
