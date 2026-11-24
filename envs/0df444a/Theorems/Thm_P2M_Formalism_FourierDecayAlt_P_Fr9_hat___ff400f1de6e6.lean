-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_hat___ff400f1de6e6
-- name    : P2M_Formalism_FourierDecayAlt_P_Fr9_hat___ff400f1de6e6
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:02:03.700055+00:00
-- url     : https://prove2.me/theorems/16a9c880-80aa-4b5d-ab39-2f5a7415869b
-- title:
--   P2 M Formalism Fourier Decay Alt P Fr9 hat   ff400f1de6e6: P2 M Formalism Fourier Decay Alt P Fr9 hat   ff400f1de6e6
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Fr9 hat   ff400f1de6e6 construction uses the P2 M Formalism Fourier Decay Alt P Fr9 hat   ff400f1de6e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L144-L145

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

theorem P2M_Formalism_FourierDecayAlt_P_Fr9_hat___ff400f1de6e6 (h : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) : f.hatT Y 1 1 = io L.GG * f.x Y := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Fr9».«hat_τ» := P2M_Formalism_FourierDecayAlt_P_Fr9_hat___ff400f1de6e6
