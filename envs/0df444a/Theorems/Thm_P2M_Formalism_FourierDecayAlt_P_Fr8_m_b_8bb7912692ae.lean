-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_b_8bb7912692ae
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr8_m_b_8bb7912692ae
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:02:19.734802+00:00
-- url     : https://prove2.me/theorems/0175c636-c214-4f0b-aef1-f326ebce8a0d
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr8 m b 8bb7912692ae: P2 M Formalism Fourier Decay Alt P Fr8 m b 8bb7912692ae
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr8 m b 8bb7912692ae construction uses the P2 M Formalism Fourier Decay Alt P Fr8 m b 8bb7912692ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L156-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L156-L157

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr8_m_b_8bb7912692ae (L : LevelData A r) : L.ζb ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr8».«mζb» := P2M_Formalism_FourierDecayAlt_P_Fr8_m_b_8bb7912692ae
