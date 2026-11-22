-- Prove2me | Theorems.Thm_PI_OpWords_mono_val
-- name    : PI.OpWords.mono_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:25.947396+00:00
-- url     : https://prove2.me/theorems/a337bec7-ff8a-43f0-9c01-700b92540b58
-- title:
--   Op Words: mono val
-- statement:
--   The Op Words construction uses the mono val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L68-L71

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

theorem PI.OpWords.mono_val (g : Fin k →₀ ℕ) :
    (mono K k d g : MvPolynomial (Fin k) K) = if g.degree = d then monomial g 1 else 0 := by sorry
