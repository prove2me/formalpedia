-- Prove2me | Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_eval_tt
-- name    : PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.eval_tt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:35.771669+00:00
-- url     : https://prove2.me/theorems/555fdcc7-82e6-4db7-96bb-fa1a24428795
-- title:
--   Weighted Homogeneous Polynomial Differential Words: eval tt
-- statement:
--   The Weighted Homogeneous Polynomial Differential Words construction uses the eval tt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L77-L79

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

theorem PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.eval_tt (p : Fin k ⊕ Fin k → K) :
    eval p (tt K k) = ∑ i, p (Sum.inl i) * p (Sum.inr i) := by sorry
