-- Prove2me | Theorems.Thm_PI_SqPairLocal_divAt_conj
-- name    : PI.SqPairLocal.divAt_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:26:12.97537+00:00
-- url     : https://prove2.me/theorems/5c284d4f-3675-40d7-bcd2-e29b95a4724f
-- title:
--   Sq Pair Local: div At conj
-- statement:
--   The Sq Pair Local construction uses the div At conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L108-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L108-L133

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

theorem PI.SqPairLocal.divAt_conj {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ} (ϖ d : 𝓞 E) (hϖ : ϖ ≠ 0)
    (hd : d ∉ Q) (k m : ℕ) (G : Matrix (Fin N) (Fin N) (𝓞 E)) (X : Matrix (Fin N) (Fin N) E)
    (hGX : ∀ a b, algebraMap (𝓞 E) E (G a b) =
      algebraMap (𝓞 E) E d * algebraMap (𝓞 E) E ϖ ^ (2 * k) * X a b)
    (h : ∀ a b, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * G a b = ϖ ^ (2 * k + m) * w) (a b : Fin N) :
    DivAt Q (ϖ ^ m) (X a b) := by sorry
