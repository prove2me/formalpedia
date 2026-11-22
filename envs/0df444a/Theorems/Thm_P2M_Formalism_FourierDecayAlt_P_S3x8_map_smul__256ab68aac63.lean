-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_S3x8_map_smul__256ab68aac63
-- name    : P2M_Formalism_FourierDecayAlt_P_S3x8_map_smul__256ab68aac63
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:00.410202+00:00
-- url     : https://prove2.me/theorems/093f66d5-5b23-462a-97c0-25a0a647b837
-- title:
--   P2 M Formalism Fourier Decay Alt P S3x8 map smul  256ab68aac63: P2 M Formalism Fourier Decay Alt P S3x8 map smul  256ab68aac63
-- statement:
--   The P2 M Formalism Fourier Decay Alt P S3x8 map smul  256ab68aac63 construction uses the P2 M Formalism Fourier Decay Alt P S3x8 map smul  256ab68aac63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L206-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L206-L208

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A F : Type} [CommRing A] [CommRing F]

theorem P2M_Formalism_FourierDecayAlt_P_S3x8_map_smul__256ab68aac63 (f : A →+* F) {m n : Type} (c : A) (X : Matrix m n A) :
    (c • X).map f = f c • X.map f := by sorry

alias «Formalism».«FourierDecayAlt».«P».«S3x8».«map_smul'» := P2M_Formalism_FourierDecayAlt_P_S3x8_map_smul__256ab68aac63
