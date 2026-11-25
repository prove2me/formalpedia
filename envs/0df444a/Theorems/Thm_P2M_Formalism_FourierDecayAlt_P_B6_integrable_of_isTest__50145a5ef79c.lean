-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_integrable_of_isTest__50145a5ef79c
-- name    : P2M_Formalism_FourierDecayAlt_P_B6_integrable_of_isTest__50145a5ef79c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:00.532602+00:00
-- url     : https://prove2.me/theorems/178a0609-b6f8-46b3-9b07-73590ec1bcd9
-- title:
--   P2 M Formalism Fourier Decay Alt P B6 integrable of is Test  50145a5ef79c: P2 M Formalism Fourier Decay Alt P B6 integrable of is Test  50145a5ef79c
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B6 integrable of is Test  50145a5ef79c construction uses the P2 M Formalism Fourier Decay Alt P B6 integrable of is Test  50145a5ef79c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2765-L2766
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2765-L2766

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

theorem P2M_Formalism_FourierDecayAlt_P_B6_integrable_of_isTest__50145a5ef79c {w : ℝ → ℝ} (h : IsTest w) : Integrable w := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B6».«integrable_of_isTest'» := P2M_Formalism_FourierDecayAlt_P_B6_integrable_of_isTest__50145a5ef79c
