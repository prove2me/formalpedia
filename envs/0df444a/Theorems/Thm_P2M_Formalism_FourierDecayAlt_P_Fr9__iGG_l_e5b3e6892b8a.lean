-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9__iGG_l_e5b3e6892b8a
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr9__iGG_l_e5b3e6892b8a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:54.899866+00:00
-- url     : https://prove2.me/theorems/81f77cbd-264b-4944-8289-27b3c1bbfffc
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr9  i GG l e5b3e6892b8a: P2 M Formalism Fourier Decay Alt P Fr9  i GG l e5b3e6892b8a
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr9  i GG l e5b3e6892b8a construction uses the P2 M Formalism Fourier Decay Alt P Fr9  i GG l e5b3e6892b8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L499-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L499-L507

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr9__iGG_l_e5b3e6892b8a (h : IsFrame L f) (Y : ℂ) :
    io L.ζi * io L.GG * f.l L Y = (f.l L Y + kapL L * tz L) * (io L.ζi * io L.GG) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr9».«ζiGG_l» := P2M_Formalism_FourierDecayAlt_P_Fr9__iGG_l_e5b3e6892b8a
