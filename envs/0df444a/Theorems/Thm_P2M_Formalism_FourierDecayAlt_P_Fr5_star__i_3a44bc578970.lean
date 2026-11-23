-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_star__i_3a44bc578970
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr5_star__i_3a44bc578970
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:26.429209+00:00
-- url     : https://prove2.me/theorems/ae30ce67-e40f-4e11-8b90-4d63f89244bb
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr5 star  i 3a44bc578970: P2 M Formalism Fourier Decay Alt P Fr5 star  i 3a44bc578970
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr5 star  i 3a44bc578970 construction uses the P2 M Formalism Fourier Decay Alt P Fr5 star  i 3a44bc578970 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L205-L209

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_Fr5_star__i_3a44bc578970 {L : LevelData A r} (h : IsStarLevel L) : star L.ζi = L.ζbi := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr5».«star_ζi» := P2M_Formalism_FourierDecayAlt_P_Fr5_star__i_3a44bc578970
