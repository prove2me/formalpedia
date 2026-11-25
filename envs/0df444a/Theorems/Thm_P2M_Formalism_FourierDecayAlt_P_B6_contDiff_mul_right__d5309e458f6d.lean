-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_contDiff_mul_right__d5309e458f6d
-- name    : P2M_Formalism_FourierDecayAlt_P_B6_contDiff_mul_right__d5309e458f6d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:00.76005+00:00
-- url     : https://prove2.me/theorems/61c9df4e-bbdd-46db-a72e-ac434afe8acc
-- title:
--   P2 M Formalism Fourier Decay Alt P B6 cont Diff mul right  d5309e458f6d: P2 M Formalism Fourier Decay Alt P B6 cont Diff mul right  d5309e458f6d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B6 cont Diff mul right  d5309e458f6d construction uses the P2 M Formalism Fourier Decay Alt P B6 cont Diff mul right  d5309e458f6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L627-L628
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L627-L628

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_B6_contDiff_mul_right__d5309e458f6d (X : Mat k r) {n : WithTop ℕ∞} : ContDiff ℝ n (fun g : Mat k r => g * X) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B6».«contDiff_mul_right'» := P2M_Formalism_FourierDecayAlt_P_B6_contDiff_mul_right__d5309e458f6d
