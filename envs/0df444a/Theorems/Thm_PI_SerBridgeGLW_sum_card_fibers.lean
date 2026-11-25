-- Prove2me | Theorems.Thm_PI_SerBridgeGLW_sum_card_fibers
-- name    : PI.SerBridgeGLW.sum_card_fibers
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:01:10.769175+00:00
-- url     : https://prove2.me/theorems/b6b3bc3a-4054-4ffd-a9a2-643e563c486f
-- title:
--   Ser Bridge GLW: sum card fibers
-- statement:
--   The Ser Bridge GLW construction uses the sum card fibers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/ClassFnOfIsIrrChar.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/ClassFnOfIsIrrChar.lean#L8-L11

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ClassFnOfIsIrrChar
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

theorem PI.SerBridgeGLW.sum_card_fibers {r s : ℕ} (b : Fin r → Fin s) : ∑ j, Fintype.card {i // b i = j} = r := by sorry
