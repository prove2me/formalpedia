-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr10_tri_mul__7132e1048a78
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr10_tri_mul__7132e1048a78
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:04.945003+00:00
-- url     : https://prove2.me/theorems/1c18c9b8-014e-4d8d-815f-23d09f418600
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr10 tri mul  7132e1048a78: P2 M Formalism Fourier Decay Alt P Fr10 tri mul  7132e1048a78
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr10 tri mul  7132e1048a78 construction uses the P2 M Formalism Fourier Decay Alt P Fr10 tri mul  7132e1048a78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L168-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L168-L176

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {r : ℕ} (L : LevelData A r) (f : FrameData S A)

theorem P2M_Formalism_FourierDecayAlt_P_Fr10_tri_mul__7132e1048a78 (m : SlopeTestRemainingChoices S A) :
    (!![1, 0; -m, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) *
      (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * m, io L.GG]) = (1 : M2 (SlopeTestRemainingChoices S A)) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr10».«tri_mul'» := P2M_Formalism_FourierDecayAlt_P_Fr10_tri_mul__7132e1048a78
