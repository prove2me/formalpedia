-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:00.865839+00:00
-- url     : https://prove2.me/theorems/02fc39db-2280-42c8-b4af-23929e195588
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr9 m i e9f2f11151ee: P2 M Formalism Fourier Decay Alt P Fr9 m i e9f2f11151ee
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr9 m i e9f2f11151ee construction uses the P2 M Formalism Fourier Decay Alt P Fr9 m i e9f2f11151ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L62-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L62-L62

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee : L.ζi ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr9».«mζi» := P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
