-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_sigmaFinite__SS_1f0045a81b6a
-- name    : P2M_Formalism_FourierDecayAlt_P_B6_sigmaFinite__SS_1f0045a81b6a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:54:32.358142+00:00
-- url     : https://prove2.me/theorems/1216cfbe-2eac-45d0-8992-e1588067bed4
-- title:
--   P2 M Formalism Fourier Decay Alt P B6 sigma Finite  SS 1f0045a81b6a: P2 M Formalism Fourier Decay Alt P B6 sigma Finite  SS 1f0045a81b6a
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B6 sigma Finite  SS 1f0045a81b6a construction uses the P2 M Formalism Fourier Decay Alt P B6 sigma Finite  SS 1f0045a81b6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L475-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormDiagonalEntryDilationGeneratorLeOne.lean#L475-L480

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem P2M_Formalism_FourierDecayAlt_P_B6_sigmaFinite__SS_1f0045a81b6a (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μSS := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B6».«sigmaFinite_μSS» := P2M_Formalism_FourierDecayAlt_P_B6_sigmaFinite__SS_1f0045a81b6a
