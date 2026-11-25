-- Prove2me | Theorems.Thm_PI_SqPairLocal_StModel_exists_clear
-- name    : PI.SqPairLocal.StModel.exists_clear
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:53:36.721532+00:00
-- url     : https://prove2.me/theorems/b4f1ed44-d143-4f31-a8ce-17c49d9df97f
-- title:
--   St Model: exists clear
-- statement:
--   The St Model construction uses the exists clear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L43-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L43-L87

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
open PI.SqPairLocal.StModel
variable {Q : Ideal (𝓞 E)} (M : StModel E Q)

theorem PI.SqPairLocal.StModel.exists_clear [hQ : Q.IsPrime] {ι : Type} [Fintype ι] (x : ι → E) :
    ∃ k : ℕ, ∃ t : 𝓞 E, t ∉ Q ∧ ∃ w : ι → 𝓞 E,
      ∀ i, algebraMap (𝓞 E) E t * algebraMap (𝓞 E) E M.ϖ ^ k * x i = algebraMap (𝓞 E) E (w i) := by sorry
