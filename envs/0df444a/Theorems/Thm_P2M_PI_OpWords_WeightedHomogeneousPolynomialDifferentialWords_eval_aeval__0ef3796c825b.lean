-- Prove2me | Theorems.Thm_P2M_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_eval_aeval__0ef3796c825b
-- name    : P2M_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_eval_aeval__0ef3796c825b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:57.488219+00:00
-- url     : https://prove2.me/theorems/3a4d3a22-a70e-5ee7-8ab7-79d19b89f4d6
-- title:
--   P2 M PI Op Words Weighted Homogeneous Polynomial Differential Words eval aeval  0ef3796c825b: P2 M PI Op Words Weighted Homogeneous Polynomial Differential Words eval aeval  0ef3796c825b
-- statement:
--   The P2 M PI Op Words Weighted Homogeneous Polynomial Differential Words eval aeval  0ef3796c825b construction uses the P2 M PI Op Words Weighted Homogeneous Polynomial Differential Words eval aeval  0ef3796c825b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L158-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/IsWeightedHomogeneousPairingLeft.lean#L158-L160

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

theorem P2M_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_eval_aeval__0ef3796c825b (g : Fin k ⊕ Fin k → Pol K k) (p : Fin k ⊕ Fin k → K) (f : Pol K k) :
    eval p (aeval g f) = eval (fun v => eval p (g v)) f := by sorry

alias «PI».«OpWords».«WeightedHomogeneousPolynomialDifferentialWords».«eval_aeval'» := P2M_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_eval_aeval__0ef3796c825b
