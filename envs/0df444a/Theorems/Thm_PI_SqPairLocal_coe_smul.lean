-- Prove2me | Theorems.Thm_PI_SqPairLocal_coe_smul
-- name    : PI.SqPairLocal.coe_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:24:23.777363+00:00
-- url     : https://prove2.me/theorems/b4ab6704-42cf-57df-9011-d5d4801be591
-- title:
--   Sq Pair Local: coe smul
-- statement:
--   The Sq Pair Local construction uses the coe smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L128-L132

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

theorem PI.SqPairLocal.coe_smul (r : 𝓞 E) (v : Fin N → E) : (r : E) • v = r • v := by sorry
