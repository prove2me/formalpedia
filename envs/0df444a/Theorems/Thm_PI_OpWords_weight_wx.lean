-- Prove2me | Theorems.Thm_PI_OpWords_weight_wx
-- name    : PI.OpWords.weight_wx
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:17:04.540337+00:00
-- url     : https://prove2.me/theorems/faa5205d-7b2f-4ab4-8ccd-1abc48b7dac3
-- title:
--   Op Words: weight wx
-- statement:
--   The Op Words construction uses the weight wx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L180-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L180-L181

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

theorem PI.OpWords.weight_wx (m g : Fin k →₀ ℕ) : Finsupp.weight (wx k) (Finsupp.sumElim m g) = m.degree := by sorry
