-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_star__i_aadcb2435e70
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr8_star__i_aadcb2435e70
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:14.533342+00:00
-- url     : https://prove2.me/theorems/858c64ab-fcd7-4c46-8453-bb3e2df2dae6
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr8 star  i aadcb2435e70: P2 M Formalism Fourier Decay Alt P Fr8 star  i aadcb2435e70
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr8 star  i aadcb2435e70 construction uses the P2 M Formalism Fourier Decay Alt P Fr8 star  i aadcb2435e70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L175-L177

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr8_star__i_aadcb2435e70 {L : LevelData A r} (h : IsStarLevel L) : star L.ζi = L.ζbi := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr8».«star_ζi» := P2M_Formalism_FourierDecayAlt_P_Fr8_star__i_aadcb2435e70
