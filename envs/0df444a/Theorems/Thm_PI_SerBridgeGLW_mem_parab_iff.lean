-- Prove2me | Theorems.Thm_PI_SerBridgeGLW_mem_parab_iff
-- name    : PI.SerBridgeGLW.mem_parab_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:49:58.379319+00:00
-- url     : https://prove2.me/theorems/6ab51abf-c55d-4fcb-8071-c5590df3c3f0
-- title:
--   Ser Bridge GLW: mem parab iff
-- statement:
--   The Ser Bridge GLW construction uses the mem parab iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/BlockSum.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/BlockSum.lean#L11-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ClassFnOfIsIrrChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_BlockSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open PI PI.SerBridgeGLW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem PI.SerBridgeGLW.mem_parab_iff {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (p : GL ι K) :
    p ∈ parab K b ↔ IsBlockUT K b (p : Matrix ι ι K) := by sorry
