-- Prove2me | Theorems.Thm_PI_WeylForKWork_plusBlock_mul
-- name    : PI.WeylForKWork.plusBlock_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:50.155873+00:00
-- url     : https://prove2.me/theorems/9a53a2e2-0e33-540a-affb-75d3c730d920
-- title:
--   Weyl For KWork: plus Block mul
-- statement:
--   The Weyl For KWork construction uses the plus Block mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L88-L91

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

theorem PI.WeylForKWork.plusBlock_mul (ε : Fin N → Bool) (a b : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) :
    iPl ε (a * b) = iPl ε a * iPl ε b := by sorry
