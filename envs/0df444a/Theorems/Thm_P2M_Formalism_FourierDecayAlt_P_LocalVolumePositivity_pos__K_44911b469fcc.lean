-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__K_44911b469fcc
-- name    : P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__K_44911b469fcc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:42.769706+00:00
-- url     : https://prove2.me/theorems/42793c33-8bff-4c4d-9c55-b3dd935ccef5
-- title:
--   P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  K 44911b469fcc: P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  K 44911b469fcc
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  K 44911b469fcc construction uses the P2 M Formalism Fourier Decay Alt P Local Volume Positivity pos  K 44911b469fcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L16-L19

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

theorem P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__K_44911b469fcc (hP : B.Pos) : 0 < B.μK := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LocalVolumePositivity».«pos_μK» := P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__K_44911b469fcc
