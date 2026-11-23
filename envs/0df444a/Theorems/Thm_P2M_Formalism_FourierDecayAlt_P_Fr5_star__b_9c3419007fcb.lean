-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_star__b_9c3419007fcb
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr5_star__b_9c3419007fcb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:32.171774+00:00
-- url     : https://prove2.me/theorems/1d407d75-9017-46db-966d-08af48a827be
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr5 star  b 9c3419007fcb: P2 M Formalism Fourier Decay Alt P Fr5 star  b 9c3419007fcb
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr5 star  b 9c3419007fcb construction uses the P2 M Formalism Fourier Decay Alt P Fr5 star  b 9c3419007fcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L201-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L201-L203

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr5_star__b_9c3419007fcb {L : LevelData A r} (h : IsStarLevel L) : star L.ζb = L.ζ := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr5».«star_ζb» := P2M_Formalism_FourierDecayAlt_P_Fr5_star__b_9c3419007fcb
