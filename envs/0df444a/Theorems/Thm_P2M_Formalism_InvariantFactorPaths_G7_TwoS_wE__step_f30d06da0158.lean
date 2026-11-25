-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_TwoS_wE__step_f30d06da0158
-- name    : P2M_Formalism_InvariantFactorPaths_G7_TwoS_wE__step_f30d06da0158
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:47.343314+00:00
-- url     : https://prove2.me/theorems/0225301f-da10-47ab-b209-f1cb38d39801
-- title:
--   P2 M Formalism Invariant Factor Paths G7 Two S w E  step f30d06da0158: P2 M Formalism Invariant Factor Paths G7 Two S w E  step f30d06da0158
-- statement:
--   The P2 M Formalism Invariant Factor Paths G7 Two S w E  step f30d06da0158 construction uses the P2 M Formalism Invariant Factor Paths G7 Two S w E  step f30d06da0158 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L382-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L382-L388

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

theorem P2M_Formalism_InvariantFactorPaths_G7_TwoS_wE__step_f30d06da0158 {p : ℕ} (hp : p ≠ 0) {u : ZMod (2 * ν) → K}
    (hu2 : ∀ s, ‖u (s + 1) - u s ^ p‖ ≤ (p : ℝ)⁻¹) (k : ℕ) (s : ZMod (2 * ν)) :
    ‖wE u k s ^ p - wE' u k s‖ ≤ (p : ℝ)⁻¹ := by sorry

alias «Formalism».«InvariantFactorPaths».«G7».«TwoS».«wE'_step» := P2M_Formalism_InvariantFactorPaths_G7_TwoS_wE__step_f30d06da0158
