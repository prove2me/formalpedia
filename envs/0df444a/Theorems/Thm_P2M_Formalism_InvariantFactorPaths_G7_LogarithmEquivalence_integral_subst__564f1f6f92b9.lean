-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9
-- name    : P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:48.89467+00:00
-- url     : https://prove2.me/theorems/491ce9f6-43ce-4bdd-a80c-9c8b8a66be02
-- title:
--   P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence integral subst  564f1f6f92b9: P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence integral subst  564f1f6f92b9
-- statement:
--   The P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence integral subst  564f1f6f92b9 construction uses the P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence integral subst  564f1f6f92b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L55-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L55-L67

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

theorem P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9 {K ι κ : Type} [Finite ι] [NormedField K] [IsUltrametricDist K]
    {f : MvPowerSeries ι K} {φ : ι → MvPowerSeries κ K}
    (h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hφ : ∀ i, Integral (φ i))
    (hf : Integral f) : Integral (MvPowerSeries.subst φ f) := by sorry

alias «Formalism».«InvariantFactorPaths».«G7».«LogarithmEquivalence».«integral_subst'» := P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9
