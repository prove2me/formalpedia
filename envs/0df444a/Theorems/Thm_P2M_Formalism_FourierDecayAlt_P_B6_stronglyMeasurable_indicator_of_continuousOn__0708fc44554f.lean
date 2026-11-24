-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_stronglyMeasurable_indicator_of_continuousOn__0708fc44554f
-- name    : P2M_Formalism_FourierDecayAlt_P_B6_stronglyMeasurable_indicator_of_continuousOn__0708fc44554f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:38:46.262865+00:00
-- url     : https://prove2.me/theorems/10896dc4-270a-4e1b-8051-19a80195c525
-- title:
--   P2 M Formalism Fourier Decay Alt P B6 strongly Measurable indicator of continuous On  0708fc44554f: P2 M Formalism Fourier Decay Alt P B6 strongly Measurable indicator of continuous On  0708fc44554f
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B6 strongly Measurable indicator of continuous On  0708fc44554f construction uses the P2 M Formalism Fourier Decay Alt P B6 strongly Measurable indicator of continuous On  0708fc44554f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2218-L2223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2218-L2223

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem P2M_Formalism_FourierDecayAlt_P_B6_stronglyMeasurable_indicator_of_continuousOn__0708fc44554f {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {s : Set X} (hs : MeasurableSet s) {f : X → ℂ} (hf : ContinuousOn f s) :
    StronglyMeasurable (s.indicator f) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B6».«stronglyMeasurable_indicator_of_continuousOn'» := P2M_Formalism_FourierDecayAlt_P_B6_stronglyMeasurable_indicator_of_continuousOn__0708fc44554f
