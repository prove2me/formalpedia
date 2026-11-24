-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_Et_zero__544253459110
-- name    : P2M_Formalism_FourierDecayAlt_P_B6_Et_zero__544253459110
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:00:33.79264+00:00
-- url     : https://prove2.me/theorems/9e729098-34cb-4f61-9b85-72d32b288f0b
-- title:
--   P2 M Formalism Fourier Decay Alt P B6 Et zero  544253459110: P2 M Formalism Fourier Decay Alt P B6 Et zero  544253459110
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B6 Et zero  544253459110 construction uses the P2 M Formalism Fourier Decay Alt P B6 Et zero  544253459110 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2215-L2216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L2215-L2216

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

theorem P2M_Formalism_FourierDecayAlt_P_B6_Et_zero__544253459110 (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : ¬ D.inSS p)
    (t : ℝ × ℝ) : Et D F F' (p, t) = 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B6».«Et_zero'» := P2M_Formalism_FourierDecayAlt_P_B6_Et_zero__544253459110
