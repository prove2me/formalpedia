-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B7_norm_pi__le_53d20754f3c3
-- name    : P2M_Formalism_FourierDecayAlt_P_B7_norm_pi__le_53d20754f3c3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:32.920801+00:00
-- url     : https://prove2.me/theorems/3cd3f60c-1f83-4650-b7f1-28a6698fabc6
-- title:
--   P2 M Formalism Fourier Decay Alt P B7 norm pi  le 53d20754f3c3: P2 M Formalism Fourier Decay Alt P B7 norm pi  le 53d20754f3c3
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B7 norm pi  le 53d20754f3c3 construction uses the P2 M Formalism Fourier Decay Alt P B7 norm pi  le 53d20754f3c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L157-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L157-L158

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
attribute [local instance] sfG sfW sfN sfW'
attribute [local instance] sfSS

theorem P2M_Formalism_FourierDecayAlt_P_B7_norm_pi__le_53d20754f3c3 (D : RealPlaceData k r Wp Wq) {h : Mat k r} (hh : h ∈ UWset k r D.z') : ‖D.π' h‖ ≤ 1 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B7».«norm_pi'_le» := P2M_Formalism_FourierDecayAlt_P_B7_norm_pi__le_53d20754f3c3
