-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_bdd_smul__b5f706ad7ca8
-- name    : P2M_Formalism_FourierDecayAlt_P_E2_bdd_smul__b5f706ad7ca8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:35.024235+00:00
-- url     : https://prove2.me/theorems/a007f663-acc7-4574-842a-a9c6ffee4174
-- title:
--   P2 M Formalism Fourier Decay Alt P E2 bdd smul  b5f706ad7ca8: P2 M Formalism Fourier Decay Alt P E2 bdd smul  b5f706ad7ca8
-- statement:
--   The P2 M Formalism Fourier Decay Alt P E2 bdd smul  b5f706ad7ca8 construction uses the P2 M Formalism Fourier Decay Alt P E2 bdd smul  b5f706ad7ca8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MiddleThirdEstimate.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MiddleThirdEstimate.lean#L68-L72

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.E2
open Formalism.FourierDecayAlt.E Real Polynomial MeasureTheory

theorem P2M_Formalism_FourierDecayAlt_P_E2_bdd_smul__b5f706ad7ca8 {Λ : Type} {f : Λ → ℂ} (c : ℂ) (hf : Bdd f) : Bdd (c • f) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«E2».«bdd_smul'» := P2M_Formalism_FourierDecayAlt_P_E2_bdd_smul__b5f706ad7ca8
