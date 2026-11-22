-- Prove2me | Theorems.Thm_PI_WeylForKWork_minusBlock_eq_blockReindex
-- name    : PI.WeylForKWork.minusBlock_eq_blockReindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:23.907619+00:00
-- url     : https://prove2.me/theorems/288e642e-98e5-4f00-bd9f-f48fa7fb49fb
-- title:
--   Weyl For KWork: minus Block eq block Reindex
-- statement:
--   The Weyl For KWork construction uses the minus Block eq block Reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L21-L22

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

theorem PI.WeylForKWork.minusBlock_eq_blockReindex (ε : Fin N → Bool) (h : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) :
    iMi ε h = blR ε (fromBlocks 1 0 0 h) := by sorry
