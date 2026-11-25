-- Prove2me | Theorems.Thm_PI_SlopeSteps_fockQ_eq_sum
-- name    : PI.SlopeSteps.fockQ_eq_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:20.782821+00:00
-- url     : https://prove2.me/theorems/d4b93ae7-8be0-47cf-a3ea-e85efecd3e06
-- title:
--   Slope Steps: fock Q eq sum
-- statement:
--   The Slope Steps construction uses the fock Q eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/NablaGram.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/NablaGram.lean#L64-L70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV Matrix

theorem PI.SlopeSteps.fockQ_eq_sum {σ : Type} (P Q : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    fockQ P Q = ∑ m ∈ S, P.coeff m * Q.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by sorry
