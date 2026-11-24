-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_star__b_1c4832101cb0
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr3_star__b_1c4832101cb0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:00:53.572147+00:00
-- url     : https://prove2.me/theorems/9b538eec-2f0b-46ed-919a-83d5782a72e1
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr3 star  b 1c4832101cb0: P2 M Formalism Fourier Decay Alt P Fr3 star  b 1c4832101cb0
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr3 star  b 1c4832101cb0 construction uses the P2 M Formalism Fourier Decay Alt P Fr3 star  b 1c4832101cb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L163-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean#L163-L163

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ} {L : LevelData A r} {f : FrameData S A}

theorem P2M_Formalism_FourierDecayAlt_P_Fr3_star__b_1c4832101cb0 (hL : IsStarLevel L) : star L.ζb = L.ζ := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr3».«star_ζb» := P2M_Formalism_FourierDecayAlt_P_Fr3_star__b_1c4832101cb0
