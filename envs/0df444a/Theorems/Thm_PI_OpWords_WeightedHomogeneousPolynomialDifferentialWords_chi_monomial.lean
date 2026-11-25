-- Prove2me | Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_chi_monomial
-- name    : PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.chi_monomial
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:40.700188+00:00
-- url     : https://prove2.me/theorems/45a29eff-47c5-4217-b8fc-e23f5dce68b9
-- title:
--   Weighted Homogeneous Polynomial Differential Words: chi monomial
-- statement:
--   The Weighted Homogeneous Polynomial Differential Words construction uses the chi monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L123-L129

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

theorem PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.chi_monomial (i0 : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) (c : K) :
    aeval (chiF K i0) (monomial m c : Pol K k) =
      X (Sum.inl i0) ^ (Finsupp.weight (wxi k) m) * monomial m c := by sorry
