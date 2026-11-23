-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
-- name    : P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:55.422578+00:00
-- url     : https://prove2.me/theorems/60406272-4e7c-4423-ad12-740635261a56
-- title:
--   P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence integral mul  d725f3beb1b3: P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence integral mul  d725f3beb1b3
-- statement:
--   The P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence integral mul  d725f3beb1b3 construction uses the P2 M Formalism Invariant Factor Paths G7 Logarithm Equivalence integral mul  d725f3beb1b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L38-L42

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

theorem P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3 {K ι : Type} [NormedField K] [IsUltrametricDist K] {f g : MvPowerSeries ι K}
    (hf : Integral f) (hg : Integral g) : Integral (f * g) := by sorry

alias «Formalism».«InvariantFactorPaths».«G7».«LogarithmEquivalence».«integral_mul'» := P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
