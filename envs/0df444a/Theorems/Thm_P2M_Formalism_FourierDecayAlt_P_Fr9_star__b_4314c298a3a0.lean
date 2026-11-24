-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_star__b_4314c298a3a0
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr9_star__b_4314c298a3a0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:04:39.020804+00:00
-- url     : https://prove2.me/theorems/a09942dc-52bf-4eea-8c7d-8a4c54ca753d
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr9 star  b 4314c298a3a0: P2 M Formalism Fourier Decay Alt P Fr9 star  b 4314c298a3a0
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr9 star  b 4314c298a3a0 construction uses the P2 M Formalism Fourier Decay Alt P Fr9 star  b 4314c298a3a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L70-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L70-L70

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
variable {L}

theorem P2M_Formalism_FourierDecayAlt_P_Fr9_star__b_4314c298a3a0 (hS : IsStarLevel L) : star L.ζb = L.ζ := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr9».«star_ζb» := P2M_Formalism_FourierDecayAlt_P_Fr9_star__b_4314c298a3a0
