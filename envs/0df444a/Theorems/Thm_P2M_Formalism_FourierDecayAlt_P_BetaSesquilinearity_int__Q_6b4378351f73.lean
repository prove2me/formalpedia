-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_int__Q_6b4378351f73
-- name    : P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_int__Q_6b4378351f73
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:03.963426+00:00
-- url     : https://prove2.me/theorems/5e3d08dd-42a6-4af8-a6a9-e465b78bd5f6
-- title:
--   P2 M Formalism Fourier Decay Alt P Beta Sesquilinearity int  Q 6b4378351f73: P2 M Formalism Fourier Decay Alt P Beta Sesquilinearity int  Q 6b4378351f73
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Beta Sesquilinearity int  Q 6b4378351f73 construction uses the P2 M Formalism Fourier Decay Alt P Beta Sesquilinearity int  Q 6b4378351f73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L1149-L1156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L1149-L1156

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_int__Q_6b4378351f73 (D : RealPlaceData k r Wp Wq) (f : (Fin r → ℂ) × ℂ → ℂ) :
    ∫ q, f q ∂μQ D = ∫ q, (wt D q : ℂ) * f q := by sorry

alias «Formalism».«FourierDecayAlt».«P».«BetaSesquilinearity».«int_μQ» := P2M_Formalism_FourierDecayAlt_P_BetaSesquilinearity_int__Q_6b4378351f73
