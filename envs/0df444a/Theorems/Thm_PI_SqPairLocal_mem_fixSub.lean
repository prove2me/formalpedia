-- Prove2me | Theorems.Thm_PI_SqPairLocal_mem_fixSub
-- name    : PI.SqPairLocal.mem_fixSub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:34:16.264894+00:00
-- url     : https://prove2.me/theorems/efdc447f-5916-4dfd-af67-faa245735688
-- title:
--   Sq Pair Local: mem fix Sub
-- statement:
--   The Sq Pair Local construction uses the mem fix Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/MemFixSub.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/MemFixSub.lean#L12-L13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal

theorem PI.SqPairLocal.mem_fixSub {R : Type} [CommRing R] (σ : R ≃+* R) (x : R) : x ∈ fixSub σ ↔ σ x = x := by sorry
