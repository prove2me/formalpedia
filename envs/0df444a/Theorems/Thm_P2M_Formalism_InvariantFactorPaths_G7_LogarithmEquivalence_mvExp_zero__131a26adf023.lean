-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mvExp_zero__131a26adf023
-- name    : P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mvExp_zero__131a26adf023
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:45.991257+00:00
-- url     : https://prove2.me/theorems/17f30741-585a-4856-bb3f-912922be4c2e
-- title:
--   P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence mv Exp zero  131a26adf023: P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence mv Exp zero  131a26adf023
-- statement:
--   The P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence mv Exp zero  131a26adf023 construction uses the P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence mv Exp zero  131a26adf023 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L83-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L83-L91

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence

theorem P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mvExp_zero__131a26adf023 {K ι : Type} [NormedField K] [CharZero K] :
    mvExp (0 : MvPowerSeries ι K) = 1 := by sorry

alias «Formalism».«InvariantFactorPaths».«G7».«LogarithmEquivalence».«mvExp_zero'» := P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mvExp_zero__131a26adf023
