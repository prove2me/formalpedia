-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_mvExp__1e315831da0a
-- name    : P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_mvExp__1e315831da0a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:09.127178+00:00
-- url     : https://prove2.me/theorems/47f8e635-505a-48ee-ad86-cb985f463255
-- title:
--   P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence constant Coeff mv Exp  1e315831da0a: P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence constant Coeff mv Exp  1e315831da0a
-- statement:
--   The P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence constant Coeff mv Exp  1e315831da0a construction uses the P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence constant Coeff mv Exp  1e315831da0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L93-L96

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

theorem P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_mvExp__1e315831da0a {K ι : Type} [NormedField K] [CharZero K] {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (mvExp f) = 1 := by sorry

alias «Formalism».«InvariantFactorPaths».«G7».«LogarithmEquivalence».«constantCoeff_mvExp'» := P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_mvExp__1e315831da0a
