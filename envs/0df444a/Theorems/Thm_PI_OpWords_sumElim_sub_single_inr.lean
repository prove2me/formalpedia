-- Prove2me | Theorems.Thm_PI_OpWords_sumElim_sub_single_inr
-- name    : PI.OpWords.sumElim_sub_single_inr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:50.04644+00:00
-- url     : https://prove2.me/theorems/5547abc1-cf24-590e-8ed1-d07985af8855
-- title:
--   Op Words: sum Elim sub single inr
-- statement:
--   The Op Words construction uses the sum Elim sub single inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L45-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] {k d : ℕ}

theorem PI.OpWords.sumElim_sub_single_inr (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g - single (Sum.inr b) 1 = Finsupp.sumElim m (g - single b 1) := by sorry
