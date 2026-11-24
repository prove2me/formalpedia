-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_Bt_zero__4cb6bf3235ab
-- name    : P2M_Formalism_FourierDecayAlt_P_B6_Bt_zero__4cb6bf3235ab
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:00:44.860597+00:00
-- url     : https://prove2.me/theorems/ea06c531-b6bd-4bd6-abc9-35e7b38d5025
-- title:
--   P2 M Formalism Fourier Decay Alt P B6 Bt zero  4cb6bf3235ab: P2 M Formalism Fourier Decay Alt P B6 Bt zero  4cb6bf3235ab
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B6 Bt zero  4cb6bf3235ab construction uses the P2 M Formalism Fourier Decay Alt P B6 Bt zero  4cb6bf3235ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2321-L2322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2321-L2322

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

theorem P2M_Formalism_FourierDecayAlt_P_B6_Bt_zero__4cb6bf3235ab (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : ¬ D.inSS p)
    (t : ℝ × ℝ) : Bt D F F' (p, t) = 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B6».«Bt_zero'» := P2M_Formalism_FourierDecayAlt_P_B6_Bt_zero__4cb6bf3235ab
