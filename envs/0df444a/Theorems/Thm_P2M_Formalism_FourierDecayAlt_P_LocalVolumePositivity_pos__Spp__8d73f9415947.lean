-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Spp__8d73f9415947
-- name    : P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Spp__8d73f9415947
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:57.028801+00:00
-- url     : https://prove2.me/theorems/6869d679-561a-48a0-8b6a-b56c2306d9df
-- title:
--   P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  Spp  8d73f9415947: P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  Spp  8d73f9415947
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  Spp  8d73f9415947 construction uses the P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  Spp  8d73f9415947 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L46-L49

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

theorem P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Spp__8d73f9415947 (hP : B.Pos) : 0 < B.μSpp' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LocalVolumePositivity».«pos_μSpp'» := P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Spp__8d73f9415947
