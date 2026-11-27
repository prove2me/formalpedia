-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_DivisorInequalityBounds_vw_pow__d3d9400f911c
-- name    : P2M_Formalism_DivisionValues_DivisorInequalityBounds_vw_pow__d3d9400f911c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:23.388204+00:00
-- url     : https://prove2.me/theorems/edd69801-52cc-5f3a-8ec6-84d8e774f231
-- title:
--   P2 M Formalism Division Values Divisor Inequality Bounds vw pow  d3d9400f911c: P2 M Formalism Division Values Divisor Inequality Bounds vw pow  d3d9400f911c
-- statement:
--   The P2 M Formalism Division Values Divisor Inequality Bounds vw pow  d3d9400f911c construction uses the P2 M Formalism Division Values Divisor Inequality Bounds vw pow  d3d9400f911c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean#L109-L114

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_WeightedPlaceLogSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.RationalHermitianForm Formalism.DivisionValues.StepBAux Formalism.DivisionValues.ConjugateWeightGram
open Formalism.DivisionValues.DivisorInequalityBounds

theorem P2M_Formalism_DivisionValues_DivisorInequalityBounds_vw_pow__d3d9400f911c {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (a : K)
    (ha : a ≠ 0) (n : ℕ) : vw w (a ^ n) = n * vw w a := by sorry

alias «Formalism».«DivisionValues».«DivisorInequalityBounds».«vw_pow'» := P2M_Formalism_DivisionValues_DivisorInequalityBounds_vw_pow__d3d9400f911c
