-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_caseA_PA
-- name    : PI.SqfRootsInj.W.caseA_PA
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:16.487185+00:00
-- url     : https://prove2.me/theorems/ed0a48a4-8e2e-47e4-8759-45d8dd2838c8
-- title:
--   W: case A PA
-- statement:
--   The W construction uses the case A PA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L54-L66

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab

theorem PI.SqfRootsInj.W.caseA_PA {g r ℓ : ℕ} [hg : Fact g.Prime] {f : (ZMod g)[X]} (hℓ : ℓ.Prime)
    (hB : ℓ ∉ BB r g) (h : CaseA g r ℓ f) : PA g r f := by sorry
