-- Prove2me | Theorems.Thm_PI_OpWords_prodFact_add_single
-- name    : PI.OpWords.prodFact_add_single
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:22.529952+00:00
-- url     : https://prove2.me/theorems/e60fa32c-ce0c-5f8b-9d72-1bfce87b153e
-- title:
--   Op Words: prod Fact add single
-- statement:
--   The Op Words construction uses the prod Fact add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L128-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L128-L139

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

theorem PI.OpWords.prodFact_add_single (g : Fin k →₀ ℕ) (i : Fin k) :
    (g + single i 1).prod (fun _ n => (n.factorial : K)) =
      ((g i : K) + 1) * g.prod (fun _ n => (n.factorial : K)) := by sorry
