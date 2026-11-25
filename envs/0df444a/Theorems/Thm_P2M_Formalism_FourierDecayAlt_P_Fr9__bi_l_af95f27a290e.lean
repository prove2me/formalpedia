-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9__bi_l_af95f27a290e
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr9__bi_l_af95f27a290e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:37.876032+00:00
-- url     : https://prove2.me/theorems/c0002f51-8604-4f7d-8a48-f3fe7c876d2c
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr9  bi l af95f27a290e: P2 M Formalism Fourier Decay Alt P Fr9  bi l af95f27a290e
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr9  bi l af95f27a290e construction uses the P2 M Formalism Fourier Decay Alt P Fr9  bi l af95f27a290e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L487-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L487-L490

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}

theorem P2M_Formalism_FourierDecayAlt_P_Fr9__bi_l_af95f27a290e (h : IsFrame L f) (Y : ℂ) : io L.ζbi * f.l L Y = f.l L Y * io L.ζbi := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr9».«ζbi_l» := P2M_Formalism_FourierDecayAlt_P_Fr9__bi_l_af95f27a290e
