-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B4_op__contDiffOn_a13b807b4df6
-- name    : P2M_Formalism_FourierDecayAlt_P_B4_op__contDiffOn_a13b807b4df6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:28:48.1121+00:00
-- url     : https://prove2.me/theorems/ada7c9c7-f5b7-4bd9-ae2d-b9944cee1ea6
-- title:
--   P2 M Formalism Fourier Decay Alt P B4 op  cont Diff On a13b807b4df6: P2 M Formalism Fourier Decay Alt P B4 op  cont Diff On a13b807b4df6
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B4 op  cont Diff On a13b807b4df6 construction uses the P2 M Formalism Fourier Decay Alt P B4 op  cont Diff On a13b807b4df6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L291-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L291-L294

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_B4_op__contDiffOn_a13b807b4df6 {f' : Mat k r → E} {U : Set (Mat k r)} (m : ℕ) (b : Bool) (X : Mat k r)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U) :
    ContDiffOn ℝ (((m : ℕ) : ℕ∞) : WithTop ℕ∞) (op' b X f') U := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B4».«op'_contDiffOn» := P2M_Formalism_FourierDecayAlt_P_B4_op__contDiffOn_a13b807b4df6
