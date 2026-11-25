-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_star__bi_58cd25344a8d
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr8_star__bi_58cd25344a8d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:24.213603+00:00
-- url     : https://prove2.me/theorems/a56d81a4-c61e-44c8-b12e-7f0608e23b80
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr8 star  bi 58cd25344a8d: P2 M Formalism Fourier Decay Alt P Fr8 star  bi 58cd25344a8d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr8 star  bi 58cd25344a8d construction uses the P2 M Formalism Fourier Decay Alt P Fr8 star  bi 58cd25344a8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L179-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L179-L179

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr8_star__bi_58cd25344a8d {L : LevelData A r} (h : IsStarLevel L) : star L.ζbi = L.ζi := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr8».«star_ζbi» := P2M_Formalism_FourierDecayAlt_P_Fr8_star__bi_58cd25344a8d
