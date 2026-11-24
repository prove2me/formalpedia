-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B4_op_eq_op__514f38137870
-- name    : P2M_Formalism_FourierDecayAlt_P_B4_op_eq_op__514f38137870
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:06.875996+00:00
-- url     : https://prove2.me/theorems/66bf62a0-f57b-4f0a-bc26-1f63bb87e529
-- title:
--   P2 M Formalism Fourier Decay Alt P B4 op eq op  514f38137870: P2 M Formalism Fourier Decay Alt P B4 op eq op  514f38137870
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B4 op eq op  514f38137870 construction uses the P2 M Formalism Fourier Decay Alt P B4 op eq op  514f38137870 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L296-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L296-L303

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

theorem P2M_Formalism_FourierDecayAlt_P_B4_op_eq_op__514f38137870 {f f' : Mat k r → E} {U : Set (Mat k r)} {X : Mat k r} (m : ℕ) (b : Bool)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) (hX : inLie k r X) :
    ∀ g ∈ U, g ∈ GV k r → op b X f g = op' b X f' g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B4».«op_eq_op'» := P2M_Formalism_FourierDecayAlt_P_B4_op_eq_op__514f38137870
