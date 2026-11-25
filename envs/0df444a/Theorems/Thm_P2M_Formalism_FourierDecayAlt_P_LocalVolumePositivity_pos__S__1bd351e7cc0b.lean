-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__S__1bd351e7cc0b
-- name    : P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__S__1bd351e7cc0b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:45.848934+00:00
-- url     : https://prove2.me/theorems/8eaff76e-8839-4a1c-8d34-580c027f2916
-- title:
--   P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  S  1bd351e7cc0b: P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  S  1bd351e7cc0b
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  S  1bd351e7cc0b construction uses the P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  S  1bd351e7cc0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L36-L39

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3
open Formalism.FourierDecayAlt.P.LocalVolumePositivity
variable {P : Type} [Fintype P] {B : MassData P}

theorem P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__S__1bd351e7cc0b (hP : B.Pos) : 0 < B.μS' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LocalVolumePositivity».«pos_μS'» := P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__S__1bd351e7cc0b
