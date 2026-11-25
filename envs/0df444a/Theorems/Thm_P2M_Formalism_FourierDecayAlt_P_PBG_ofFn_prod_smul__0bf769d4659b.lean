-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBG_ofFn_prod_smul__0bf769d4659b
-- name    : P2M_Formalism_FourierDecayAlt_P_PBG_ofFn_prod_smul__0bf769d4659b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:37:53.938885+00:00
-- url     : https://prove2.me/theorems/e67476aa-820e-408d-80b8-fea4b25936eb
-- title:
--   P2 M Formalism Fourier Decay Alt P PBG of Fn prod smul  0bf769d4659b: P2 M Formalism Fourier Decay Alt P PBG of Fn prod smul  0bf769d4659b
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBG of Fn prod smul  0bf769d4659b construction uses the P2 M Formalism Fourier Decay Alt P PBG of Fn prod smul  0bf769d4659b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean#L246-L251

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_PBG_ofFn_prod_smul__0bf769d4659b : ∀ {n : ℕ} (c : Fin n → ℂ) (X : Fin n → A),
    (List.ofFn fun i => c i • X i).prod = (∏ i, c i) • (List.ofFn X).prod
  := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBG».«ofFn_prod_smul'» := P2M_Formalism_FourierDecayAlt_P_PBG_ofFn_prod_smul__0bf769d4659b
