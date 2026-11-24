-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_toStd_size__257163185415
-- name    : P2M_Formalism_FourierDecayAlt_P_PBD_toStd_size__257163185415
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:32:32.869861+00:00
-- url     : https://prove2.me/theorems/ffba03ce-defe-40e3-a776-e29909da1095
-- title:
--   P2 M Formalism Fourier Decay Alt P PBD to Std size  257163185415: P2 M Formalism Fourier Decay Alt P PBD to Std size  257163185415
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBD to Std size  257163185415 construction uses the P2 M Formalism Fourier Decay Alt P PBD to Std size  257163185415 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L18-L23

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix

theorem P2M_Formalism_FourierDecayAlt_P_PBD_toStd_size__257163185415 (r : ℕ) (g : ℝ) : ∀ (p : C.LPt) (b : ℕ), D.ptSize (D.toStd r g b p) = D.ptSize p
  := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBD».«toStd_size'» := P2M_Formalism_FourierDecayAlt_P_PBD_toStd_size__257163185415
