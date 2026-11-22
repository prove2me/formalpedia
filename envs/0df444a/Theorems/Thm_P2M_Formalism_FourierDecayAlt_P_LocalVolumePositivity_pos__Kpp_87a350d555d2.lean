-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Kpp_87a350d555d2
-- name    : P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Kpp_87a350d555d2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:00.369134+00:00
-- url     : https://prove2.me/theorems/38fd148a-09f4-413e-b2e5-080c2f4e8e57
-- title:
--   P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  Kpp 87a350d555d2: P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  Kpp 87a350d555d2
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  Kpp 87a350d555d2 construction uses the P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  Kpp 87a350d555d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L21-L24

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

theorem P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Kpp_87a350d555d2 (hP : B.Pos) : 0 < B.μKpp := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LocalVolumePositivity».«pos_μKpp» := P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Kpp_87a350d555d2
