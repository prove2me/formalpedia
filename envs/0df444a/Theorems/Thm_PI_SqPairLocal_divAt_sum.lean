-- Prove2me | Theorems.Thm_PI_SqPairLocal_divAt_sum
-- name    : PI.SqPairLocal.divAt_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:47.990246+00:00
-- url     : https://prove2.me/theorems/dd20e24b-97ef-4193-82e0-0798885b927d
-- title:
--   Sq Pair Local: div At sum
-- statement:
--   The Sq Pair Local construction uses the div At sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L78-L80

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

theorem PI.SqPairLocal.divAt_sum {c : 𝓞 E} {ι : Type} (S : Finset ι) (f : ι → E) (h : ∀ i ∈ S, DivAt Q c (f i)) :
    DivAt Q c (∑ i ∈ S, f i) := by sorry
