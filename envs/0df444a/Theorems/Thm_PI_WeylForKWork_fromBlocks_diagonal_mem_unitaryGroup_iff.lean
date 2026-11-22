-- Prove2me | Theorems.Thm_PI_WeylForKWork_fromBlocks_diagonal_mem_unitaryGroup_iff
-- name    : PI.WeylForKWork.fromBlocks_diagonal_mem_unitaryGroup_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:37.345784+00:00
-- url     : https://prove2.me/theorems/57543e5f-7149-47e1-8078-046bd032b823
-- title:
--   Weyl For KWork: from Blocks diagonal mem unitary Group iff
-- statement:
--   The Weyl For KWork construction uses the from Blocks diagonal mem unitary Group iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L69-L74

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

theorem PI.WeylForKWork.fromBlocks_diagonal_mem_unitaryGroup_iff (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    fromBlocks A 0 0 D ∈ unitaryGroup (m ⊕ n) ℂ ↔ A ∈ unitaryGroup m ℂ ∧ D ∈ unitaryGroup n ℂ := by sorry
