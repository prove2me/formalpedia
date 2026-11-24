-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBG_contDiff_det__9a2729db1f7b
-- name    : P2M_Formalism_FourierDecayAlt_P_PBG_contDiff_det__9a2729db1f7b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:32.187304+00:00
-- url     : https://prove2.me/theorems/fd343e52-dcd4-4624-8bea-17c16f550d1d
-- title:
--   P2 M Formalism Fourier Decay Alt P PBG cont Diff det  9a2729db1f7b: P2 M Formalism Fourier Decay Alt P PBG cont Diff det  9a2729db1f7b
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBG cont Diff det  9a2729db1f7b construction uses the P2 M Formalism Fourier Decay Alt P PBG cont Diff det  9a2729db1f7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L409-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L409-L416

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_PBG_contDiff_det__9a2729db1f7b {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : X → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i j, ContDiff ℝ ⊤ (fun x => M x i j)) :
    ContDiff ℝ ⊤ (fun x => (M x).det) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBG».«contDiff_det'» := P2M_Formalism_FourierDecayAlt_P_PBG_contDiff_det__9a2729db1f7b
