-- Prove2me | Theorems.Thm_PI_GTNum_lam_succ_le
-- name    : PI.GTNum.lam_succ_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:31:11.872382+00:00
-- url     : https://prove2.me/theorems/646edac3-e6d2-467a-bc24-5e01e2f17a95
-- title:
--   GTNum: lam succ le
-- statement:
--   The GTNum construction uses the lam succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L64-L65

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

theorem PI.GTNum.lam_succ_le (i : Fin n) : lam.w ⟨i.1 + 1, by omega⟩ ≤ lam.w ⟨i.1, by omega⟩ := by sorry
