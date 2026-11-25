-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_TwoS_integral_posW__09bbc0735fe1
-- name    : P2M_Formalism_InvariantFactorPaths_G7_TwoS_integral_posW__09bbc0735fe1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:41.936554+00:00
-- url     : https://prove2.me/theorems/8a1b96a2-7d55-47e1-aad3-700f405aca5f
-- title:
--   P2 M Formalism Invariant Factor Paths G7 Two S integral pos W  09bbc0735fe1: P2 M Formalism Invariant Factor Paths G7 Two S integral pos W  09bbc0735fe1
-- statement:
--   The P2 M Formalism Invariant Factor Paths G7 Two S integral pos W  09bbc0735fe1 construction uses the P2 M Formalism Invariant Factor Paths G7 Two S integral pos W  09bbc0735fe1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L396-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L396-L399

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
variable {r0 r1 : ℕ}

theorem P2M_Formalism_InvariantFactorPaths_G7_TwoS_integral_posW__09bbc0735fe1 [NeZero ν] (p : ℕ) {w : ZMod (2 * ν) → K} (hw : ∀ s, ‖w s‖ ≤ 1)
    (ab : Fin r0 × Fin r1) : Integral (posW' p w ab) := by sorry

alias «Formalism».«InvariantFactorPaths».«G7».«TwoS».«integral_posW'» := P2M_Formalism_InvariantFactorPaths_G7_TwoS_integral_posW__09bbc0735fe1
