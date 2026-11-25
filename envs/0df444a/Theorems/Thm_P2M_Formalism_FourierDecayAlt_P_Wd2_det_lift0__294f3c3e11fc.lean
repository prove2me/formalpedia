-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd2_det_lift0__294f3c3e11fc
-- name    : P2M_Formalism_FourierDecayAlt_P_Wd2_det_lift0__294f3c3e11fc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:31.634809+00:00
-- url     : https://prove2.me/theorems/e86dfd96-56cf-4fb6-b9d0-1c6055d2b3e4
-- title:
--   P2 M Formalism Fourier Decay Alt P Wd2 det lift0  294f3c3e11fc: P2 M Formalism Fourier Decay Alt P Wd2 det lift0  294f3c3e11fc
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Wd2 det lift0  294f3c3e11fc construction uses the P2 M Formalism Fourier Decay Alt P Wd2 det lift0  294f3c3e11fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L291-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L291-L294

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem P2M_Formalism_FourierDecayAlt_P_Wd2_det_lift0__294f3c3e11fc (M M' : M2 A) (c : K) (H : M * YangianSpanCharacter.T.J A * M'ᵀ = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (lift0 M')ᵀ = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Wd2».«det_lift0'» := P2M_Formalism_FourierDecayAlt_P_Wd2_det_lift0__294f3c3e11fc
