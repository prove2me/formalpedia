-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_star__bi_ef3e65c928e2
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr5_star__bi_ef3e65c928e2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:19.438528+00:00
-- url     : https://prove2.me/theorems/c9904368-1efb-45a9-8ce0-c00b2e08760a
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr5 star  bi ef3e65c928e2: P2 M Formalism Fourier Decay Alt P Fr5 star  bi ef3e65c928e2
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr5 star  bi ef3e65c928e2 construction uses the P2 M Formalism Fourier Decay Alt P Fr5 star  bi ef3e65c928e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L211-L212

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr5_star__bi_ef3e65c928e2 {L : LevelData A r} (h : IsStarLevel L) : star L.ζbi = L.ζi := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr5».«star_ζbi» := P2M_Formalism_FourierDecayAlt_P_Fr5_star__bi_ef3e65c928e2
