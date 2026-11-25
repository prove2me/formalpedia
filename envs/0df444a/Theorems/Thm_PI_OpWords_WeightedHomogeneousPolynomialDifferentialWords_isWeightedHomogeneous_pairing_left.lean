-- Prove2me | Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_isWeightedHomogeneous_pairing_left
-- name    : PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.isWeightedHomogeneous_pairing_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:57.459123+00:00
-- url     : https://prove2.me/theorems/836414c2-dd0c-4a6c-81db-b8b6a604599e
-- title:
--   Weighted Homogeneous Polynomial Differential Words: is Weighted Homogeneous pairing left
-- statement:
--   The Weighted Homogeneous Polynomial Differential Words construction uses the is Weighted Homogeneous pairing left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L61-L67

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

theorem PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.isWeightedHomogeneous_pairing_left : IsWeightedHomogeneous (wx k) (tt K k) 1 := by sorry
