-- Prove2me | Theorems.Thm_PI_SqPairLocal_divAt_add
-- name    : PI.SqPairLocal.divAt_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:34.263337+00:00
-- url     : https://prove2.me/theorems/f5ca226c-fa3f-43ef-b556-a7464ff63e99
-- title:
--   Sq Pair Local: div At add
-- statement:
--   The Sq Pair Local construction uses the div At add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L46-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
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
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime]

theorem PI.SqPairLocal.divAt_add {c : 𝓞 E} {x y : E} (hx : DivAt Q c x) (hy : DivAt Q c y) : DivAt Q c (x + y) := by sorry
