-- Prove2me | Theorems.Thm_PI_WeylForKWork_fromBlocks_diagonal_mul_signature_comm
-- name    : PI.WeylForKWork.fromBlocks_diagonal_mul_signature_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:10.379482+00:00
-- url     : https://prove2.me/theorems/b4f8accd-3b8b-43e2-8e79-0b50b6b1a9b2
-- title:
--   Weyl For KWork: from Blocks diagonal mul signature comm
-- statement:
--   The Weyl For KWork construction uses the from Blocks diagonal mul signature comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L76-L78

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
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem PI.WeylForKWork.fromBlocks_diagonal_mul_signature_comm (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    fromBlocks A 0 0 D * fromBlocks 1 0 0 (-1) = fromBlocks 1 0 0 (-1) * fromBlocks A 0 0 D := by sorry
