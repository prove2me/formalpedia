-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_i_b966c50babe5
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr8_m_i_b966c50babe5
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:02:10.046401+00:00
-- url     : https://prove2.me/theorems/99c8b1a8-36ed-49f5-9896-a0ba148010bb
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr8 m i b966c50babe5: P2 M Formalism Fourier Decay Alt P Fr8 m i b966c50babe5
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr8 m i b966c50babe5 construction uses the P2 M Formalism Fourier Decay Alt P Fr8 m i b966c50babe5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L154-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L154-L155

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_Fr8_m_i_b966c50babe5 (L : LevelData A r) : L.ζi ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr8».«mζi» := P2M_Formalism_FourierDecayAlt_P_Fr8_m_i_b966c50babe5
