-- Prove2me | Theorems.Thm_PI_SqPairLocal_divAt_of_map
-- name    : PI.SqPairLocal.divAt_of_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:26:16.043712+00:00
-- url     : https://prove2.me/theorems/40cf4810-894c-4ad4-890e-9893bb43ab92
-- title:
--   Sq Pair Local: div At of map
-- statement:
--   The Sq Pair Local construction uses the div At of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L99-L106

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IntAtOfDivAtZero
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
open PI.SqPair
attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PI.SqPairLocal.divAt_of_map {Q : Ideal (𝓞 E)} {N : ℕ} (A : Matrix (Fin N) (Fin N) (𝓞 E)) (c : 𝓞 E)
    (h : ∀ a b, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * A a b = c * w) (a b : Fin N) :
    DivAt Q c ((algebraMap (𝓞 E) E).mapMatrix A a b) := by sorry
