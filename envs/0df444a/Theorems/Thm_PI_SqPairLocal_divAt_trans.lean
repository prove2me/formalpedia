-- Prove2me | Theorems.Thm_PI_SqPairLocal_divAt_trans
-- name    : PI.SqPairLocal.divAt_trans
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:25:51.823857+00:00
-- url     : https://prove2.me/theorems/2d61b332-5d87-50fb-a08b-29c4c049e81f
-- title:
--   Sq Pair Local: div At trans
-- statement:
--   The Sq Pair Local construction uses the div At trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L104-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L104-L114

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

theorem PI.SqPairLocal.divAt_trans {c d : 𝓞 E} {K : ℕ}
    (hK : ∀ x ∈ Q ^ K, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w) (hd : d ∈ Q ^ K) {x : E}
    (hx : DivAt Q d x) : DivAt Q c x := by sorry
