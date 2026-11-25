-- Prove2me | Theorems.Thm_PI_WeylForKWork_sign_blockEquiv_inr
-- name    : PI.WeylForKWork.sign_blockEquiv_inr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:44:21.522604+00:00
-- url     : https://prove2.me/theorems/a6f30e20-59e7-4e60-9e6e-b3f28d8b7984
-- title:
--   Weyl For KWork: sign block Equiv inr
-- statement:
--   The Weyl For KWork construction uses the sign block Equiv inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L27-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
variable {N : ℕ}

theorem PI.WeylForKWork.sign_blockEquiv_inr (ε : Fin N → Bool) (j : Fin (nMi ε)) : ε (blk ε (Sum.inr j)) = false := by sorry
