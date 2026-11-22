-- Prove2me | Theorems.Thm_PI_WeylForKWork_blockReindex_mem_unitaryCentralizer_iff
-- name    : PI.WeylForKWork.blockReindex_mem_unitaryCentralizer_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:31.36982+00:00
-- url     : https://prove2.me/theorems/a3d6c29e-36a9-4788-8334-9db87f640d5f
-- title:
--   Weyl For KWork: block Reindex mem unitary Centralizer iff
-- statement:
--   The Weyl For KWork construction uses the block Reindex mem unitary Centralizer iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L55-L58

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

theorem PI.WeylForKWork.blockReindex_mem_unitaryCentralizer_iff (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    blR ε M ∈ Kset ε ↔ M ∈ unitaryGroup _ ℂ ∧ M * fromBlocks 1 0 0 (-1) = fromBlocks 1 0 0 (-1) * M := by sorry
