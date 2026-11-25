-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_GermFibreKernels_toStd_append__4f00116c904a
-- name    : P2M_Formalism_FourierDecayAlt_P_GermFibreKernels_toStd_append__4f00116c904a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:24.393442+00:00
-- url     : https://prove2.me/theorems/b64d777a-af0d-50e1-be62-c5fc5b2a361c
-- title:
--   P2 M Formalism Fourier Decay Alt P Germ Fibre Kernels to Std append  4f00116c904a: P2 M Formalism Fourier Decay Alt P Germ Fibre Kernels to Std append  4f00116c904a
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Germ Fibre Kernels to Std append  4f00116c904a construction uses the P2 M Formalism Fourier Decay Alt P Germ Fibre Kernels to Std append  4f00116c904a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ToStdAppend.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ToStdAppend.lean#L13-L18

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNegBetaL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ToStdAppend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermFibreKernels
open Formalism.FourierDecayAlt NumberField
noncomputable section

theorem P2M_Formalism_FourierDecayAlt_P_GermFibreKernels_toStd_append__4f00116c904a (r : ℕ) (g : ℝ) : ∀ (P Q : C.LPt) (b : ℕ),
    D.toStd r g b (P ++ Q) = D.toStd r g b P ++ D.toStd r g (b + D.ptSize P) Q
  := by sorry

alias «Formalism».«FourierDecayAlt».«P».«GermFibreKernels».«toStd_append'» := P2M_Formalism_FourierDecayAlt_P_GermFibreKernels_toStd_append__4f00116c904a
