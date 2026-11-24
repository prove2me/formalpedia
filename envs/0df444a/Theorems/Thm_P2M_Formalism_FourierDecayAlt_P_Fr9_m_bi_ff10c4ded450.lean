-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:19.329329+00:00
-- url     : https://prove2.me/theorems/297c90e7-8df6-43a5-8bda-90ac8dee0545
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr9 m bi ff10c4ded450: P2 M Formalism Fourier Decay Alt P Fr9 m bi ff10c4ded450
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr9 m bi ff10c4ded450 construction uses the P2 M Formalism Fourier Decay Alt P Fr9 m bi ff10c4ded450 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L64-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L64-L64

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450 : L.ζbi ∈ zfns L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr9».«mζbi» := P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
