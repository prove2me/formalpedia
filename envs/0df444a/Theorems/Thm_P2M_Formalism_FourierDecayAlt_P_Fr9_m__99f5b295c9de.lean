-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m__99f5b295c9de
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr9_m__99f5b295c9de
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:01:56.77831+00:00
-- url     : https://prove2.me/theorems/5fb9ce92-1aea-448a-82c4-29d1eb110b72
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr9 m  99f5b295c9de: P2 M Formalism Fourier Decay Alt P Fr9 m  99f5b295c9de
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr9 m  99f5b295c9de construction uses the P2 M Formalism Fourier Decay Alt P Fr9 m  99f5b295c9de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L61-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L61-L61

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr9_m__99f5b295c9de : L.ζ ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr9».«mζ» := P2M_Formalism_FourierDecayAlt_P_Fr9_m__99f5b295c9de
