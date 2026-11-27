-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBF_polyAction_one__8750f858715c
-- name    : P2M_Formalism_FourierDecayAlt_P_PBF_polyAction_one__8750f858715c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:38.301337+00:00
-- url     : https://prove2.me/theorems/07dc7621-fbef-5822-a0a9-05c17d5a1732
-- title:
--   P2 M Formalism Fourier Decay Alt P PBF poly Action one  8750f858715c: P2 M Formalism Fourier Decay Alt P PBF poly Action one  8750f858715c
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBF poly Action one  8750f858715c construction uses the P2 M Formalism Fourier Decay Alt P PBF poly Action one  8750f858715c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PrStarFst.lean#L31-L41

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PrStarFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBF
open Finset Formalism.FourierDecayAlt.Wd
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem P2M_Formalism_FourierDecayAlt_P_PBF_polyAction_one__8750f858715c (X : Ix S → V) : actP (1 : SlopeTestRemainingChoices S (Q.Pr V)) X = X := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBF».«polyAction_one₂» := P2M_Formalism_FourierDecayAlt_P_PBF_polyAction_one__8750f858715c
