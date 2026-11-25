-- Prove2me | Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_psi_zero
-- name    : PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.psi_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:15.671129+00:00
-- url     : https://prove2.me/theorems/339cff04-5157-58db-a9f1-47f4523c9bae
-- title:
--   Weighted Homogeneous Polynomial Differential Words: psi zero
-- statement:
--   The Weighted Homogeneous Polynomial Differential Words construction uses the psi zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L162-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L162-L191

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

theorem PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.psi_zero (i0 : Fin k) (f : Pol K k)
    (hv : ∀ p : Fin k ⊕ Fin k → K, ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → eval p f = 0) :
    aeval (psiF K i0) f = 0 := by sorry
