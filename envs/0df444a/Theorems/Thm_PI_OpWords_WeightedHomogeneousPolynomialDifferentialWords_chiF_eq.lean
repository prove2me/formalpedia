-- Prove2me | Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_chiF_eq
-- name    : PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.chiF_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:34.806066+00:00
-- url     : https://prove2.me/theorems/e4db6623-a526-5bd5-a122-64ec780fea36
-- title:
--   Weighted Homogeneous Polynomial Differential Words: chi F eq
-- statement:
--   The Weighted Homogeneous Polynomial Differential Words construction uses the chi F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L119-L121

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

theorem PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.chiF_eq (i0 : Fin k) (v : Fin k ⊕ Fin k) :
    (chiF K i0 v : Pol K k) = X v * X (Sum.inl i0) ^ (wxi k v) := by sorry
