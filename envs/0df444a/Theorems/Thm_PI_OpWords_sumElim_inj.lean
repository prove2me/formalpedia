-- Prove2me | Theorems.Thm_PI_OpWords_sumElim_inj
-- name    : PI.OpWords.sumElim_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:36.745101+00:00
-- url     : https://prove2.me/theorems/78ad4be1-1ec4-4b35-93c8-54b13fde2a4b
-- title:
--   Op Words: sum Elim inj
-- statement:
--   The Op Words construction uses the sum Elim inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L19-L31

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

theorem PI.OpWords.sumElim_inj {u g u' g' : Fin k →₀ ℕ} :
    Finsupp.sumElim u g = Finsupp.sumElim u' g' ↔ u = u' ∧ g = g' := by sorry
