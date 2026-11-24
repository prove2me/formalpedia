-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:02:10.743682+00:00
-- url     : https://prove2.me/theorems/01a7f526-d31e-4ee2-ba27-8818b4c7761c
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr9 m b c2aaaddc0865: P2 M Formalism Fourier Decay Alt P Fr9 m b c2aaaddc0865
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr9 m b c2aaaddc0865 construction uses the P2 M Formalism Fourier Decay Alt P Fr9 m b c2aaaddc0865 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L63-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L63-L63

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
variable (L : LevelData A r)

theorem P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865 : L.ζb ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr9».«mζb» := P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
