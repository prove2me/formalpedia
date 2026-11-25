-- Prove2me | Theorems.Thm_PI_SqPairLocal_pres_one_sub
-- name    : PI.SqPairLocal.pres_one_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:25:32.885314+00:00
-- url     : https://prove2.me/theorems/a59cf357-3bda-5da1-873a-6dfcd28764c6
-- title:
--   Sq Pair Local: pres one sub
-- statement:
--   The Sq Pair Local construction uses the pres one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L134-L138

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {N : ℕ}

theorem PI.SqPairLocal.pres_one_sub {L : Submodule (𝓞 E) (Fin N → E)} {e : Matrix (Fin N) (Fin N) E}
    (he : Pres L e) : Pres L (1 - e) := by sorry
