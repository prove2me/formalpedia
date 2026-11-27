-- Prove2me | Theorems.Thm_PI_SqPairLocal_StModel_detect_mat
-- name    : PI.SqPairLocal.StModel.detect_mat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:13.820904+00:00
-- url     : https://prove2.me/theorems/24064fce-dc2c-4d44-9f13-efbbe1167606
-- title:
--   St Model: detect mat
-- statement:
--   The St Model construction uses the detect mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IntAtOfDivAtZero.lean#L89-L95

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

theorem PI.SqPairLocal.StModel.detect_mat {N : ℕ} (A : Matrix (Fin N) (Fin N) (𝓞 E)) (m : ℕ)
    (Y : Matrix (Fin N) (Fin N) M.R) (h : M.j.mapMatrix A = (M.j M.ϖ ^ m) • Y) (a b : Fin N) :
    ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * A a b = M.ϖ ^ m * w := by sorry
