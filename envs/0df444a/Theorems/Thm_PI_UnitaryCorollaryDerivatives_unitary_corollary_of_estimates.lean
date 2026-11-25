-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_unitary_corollary_of_estimates
-- name    : PI.UnitaryCorollaryDerivatives.unitary_corollary_of_estimates
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:54.82197+00:00
-- url     : https://prove2.me/theorems/269903ae-df3b-479d-857b-f736dfc96fda
-- title:
--   Unitary Corollary Derivatives: unitary corollary of estimates
-- statement:
--   The Unitary Corollary Derivatives construction uses the unitary corollary of estimates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/UnitaryCorollaryOfEstimates.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/UnitaryCorollaryOfEstimates.lean#L14-L37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_UnitaryCorollaryOfEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.UnitaryCorollaryDerivatives.unitary_corollary_of_estimates (hC : CoreStar) (hD : DjWB) (hG : GfWB) (hM : WBmul) :
    Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := by sorry
