-- Prove2me | Theorems.Thm_PI_WeylForKWork_blockReindex_mem_unitaryGroup_iff
-- name    : PI.WeylForKWork.blockReindex_mem_unitaryGroup_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:45:34.287031+00:00
-- url     : https://prove2.me/theorems/9e12cd82-153f-4458-96a8-ea49f908a30c
-- title:
--   Weyl For KWork: block Reindex mem unitary Group iff
-- statement:
--   The Weyl For KWork construction uses the block Reindex mem unitary Group iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Blocks.lean#L50-L53

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

theorem PI.WeylForKWork.blockReindex_mem_unitaryGroup_iff (ε : Fin N → Bool) (M : Matrix (Fin (nPl ε) ⊕ Fin (nMi ε)) (Fin (nPl ε) ⊕ Fin (nMi ε)) ℂ) :
    blR ε M ∈ unitaryGroup (Fin N) ℂ ↔ M ∈ unitaryGroup _ ℂ := by sorry
