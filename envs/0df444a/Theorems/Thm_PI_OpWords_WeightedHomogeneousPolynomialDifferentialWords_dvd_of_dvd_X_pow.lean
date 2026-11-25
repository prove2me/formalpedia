-- Prove2me | Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_dvd_of_dvd_X_pow
-- name    : PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.dvd_of_dvd_X_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:51.681602+00:00
-- url     : https://prove2.me/theorems/242014c8-b9a6-4b7a-ab2b-95b3e5a824fe
-- title:
--   Weighted Homogeneous Polynomial Differential Words: dvd of dvd X pow
-- statement:
--   The Weighted Homogeneous Polynomial Differential Words construction uses the dvd of dvd X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L95-L102

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.dvd_of_dvd_X_pow {i : Fin k ⊕ Fin k} {s f : Pol K k} (hs : ¬ (X i : Pol K k) ∣ s) :
    ∀ n : ℕ, s ∣ X i ^ n * f → s ∣ f
  := by sorry
