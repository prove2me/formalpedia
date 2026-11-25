-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_caseB_PB
-- name    : PI.SqfRootsInj.W.caseB_PB
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:43.969992+00:00
-- url     : https://prove2.me/theorems/20c70779-4679-509d-9405-8397fb8e3c47
-- title:
--   W: case B PB
-- statement:
--   The W construction uses the case B PB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L68-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L68-L81

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

theorem PI.SqfRootsInj.W.caseB_PB {g r ℓ : ℕ} [hg : Fact g.Prime] {f : (ZMod g)[X]} (hℓ : ℓ.Prime)
    (hB : ℓ ∉ BB r g) (h : CaseB g r ℓ f) : PB g r f := by sorry
