-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B7_sm_piM__11e3047c332f
-- name    : P2M_Formalism_FourierDecayAlt_P_B7_sm_piM__11e3047c332f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:40.554353+00:00
-- url     : https://prove2.me/theorems/a31e0a8d-18fc-4371-9a4b-9abfa1663121
-- title:
--   P2 M Formalism Fourier Decay Alt P B7 sm pi M  11e3047c332f: P2 M Formalism Fourier Decay Alt P B7 sm pi M  11e3047c332f
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B7 sm pi M  11e3047c332f construction uses the P2 M Formalism Fourier Decay Alt P B7 sm pi M  11e3047c332f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L289-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L289-L290

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS
attribute [local instance] properFD

theorem P2M_Formalism_FourierDecayAlt_P_B7_sm_piM__11e3047c332f (D : RealPlaceData k r Wp Wq) : StronglyMeasurable (piM' D) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B7».«sm_piM'» := P2M_Formalism_FourierDecayAlt_P_B7_sm_piM__11e3047c332f
