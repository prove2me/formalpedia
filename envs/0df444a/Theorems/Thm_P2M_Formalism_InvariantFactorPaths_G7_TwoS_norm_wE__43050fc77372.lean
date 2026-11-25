-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_TwoS_norm_wE__43050fc77372
-- name    : P2M_Formalism_InvariantFactorPaths_G7_TwoS_norm_wE__43050fc77372
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:59.861624+00:00
-- url     : https://prove2.me/theorems/6fe3137d-8813-4ab2-bb8f-4ae15f6a7897
-- title:
--   P2 M Formalism Invariant Factor Paths G7 Two S norm w E  43050fc77372: P2 M Formalism Invariant Factor Paths G7 Two S norm w E  43050fc77372
-- statement:
--   The P2 M Formalism Invariant Factor Paths G7 Two S norm w E  43050fc77372 construction uses the P2 M Formalism Invariant Factor Paths G7 Two S norm w E  43050fc77372 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L359-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L359-L364

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open Formalism.InvariantFactorPaths.G7.TwoS
variable {ν : ℕ}
variable {K : Type}
variable [NormedField K] [IsUltrametricDist K]

theorem P2M_Formalism_InvariantFactorPaths_G7_TwoS_norm_wE__43050fc77372 {u : ZMod (2 * ν) → K} (hu : ∀ s, ‖u s‖ ≤ 1) (k : ℕ) (s : ZMod (2 * ν)) :
    ‖wE' u k s‖ ≤ 1 := by sorry

alias «Formalism».«InvariantFactorPaths».«G7».«TwoS».«norm_wE'» := P2M_Formalism_InvariantFactorPaths_G7_TwoS_norm_wE__43050fc77372
