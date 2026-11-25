-- Prove2me | Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_chi_psi_dvd
-- name    : PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.chi_psi_dvd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:38.633281+00:00
-- url     : https://prove2.me/theorems/6a0944d6-8f6b-4a1b-9d9c-5aa43dad4609
-- title:
--   Weighted Homogeneous Polynomial Differential Words: chi psi dvd
-- statement:
--   The Weighted Homogeneous Polynomial Differential Words construction uses the chi psi dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L139-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L139-L156

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

theorem PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.chi_psi_dvd (i0 : Fin k) (f : Pol K k) :
    tt K k ∣ aeval (chiF K i0) f - aeval (psiF K i0) f := by sorry
