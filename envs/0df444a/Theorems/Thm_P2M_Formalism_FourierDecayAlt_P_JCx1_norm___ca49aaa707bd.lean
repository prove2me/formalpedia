-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JCx1_norm___ca49aaa707bd
-- name    : P2M_Formalism_FourierDecayAlt_P_JCx1_norm___ca49aaa707bd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:02:23.599634+00:00
-- url     : https://prove2.me/theorems/35616fb8-f97f-41bd-a62d-b0ebd164ce4e
-- title:
--   P2 M Formalism Fourier Decay Alt P JCx1 norm   ca49aaa707bd: P2 M Formalism Fourier Decay Alt P JCx1 norm   ca49aaa707bd
-- statement:
--   The P2 M Formalism Fourier Decay Alt P JCx1 norm   ca49aaa707bd construction uses the P2 M Formalism Fourier Decay Alt P JCx1 norm   ca49aaa707bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean#L41-L46

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1
open NumberField

theorem P2M_Formalism_FourierDecayAlt_P_JCx1_norm___ca49aaa707bd {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (t : E) : ‖S.σ v t‖ = S.pl v t := by sorry

alias «Formalism».«FourierDecayAlt».«P».«JCx1».«norm_σ» := P2M_Formalism_FourierDecayAlt_P_JCx1_norm___ca49aaa707bd
