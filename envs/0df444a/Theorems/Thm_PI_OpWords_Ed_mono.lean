-- Prove2me | Theorems.Thm_PI_OpWords_Ed_mono
-- name    : PI.OpWords.Ed_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:40.073272+00:00
-- url     : https://prove2.me/theorems/d766300d-c0b2-428a-9a9b-02e62096109d
-- title:
--   Op Words: Ed mono
-- statement:
--   The Op Words construction uses the Ed mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L163-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L163-L174

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

theorem PI.OpWords.Ed_mono (a b : Fin k) (g : Fin k →₀ ℕ) :
    Formalism.MainNotions.TestSideCounting.Ed K k d a b (mono K k d g) =
      ((g b : ℕ) : K) • mono K k d (g - single b 1 + single a 1) := by sorry
