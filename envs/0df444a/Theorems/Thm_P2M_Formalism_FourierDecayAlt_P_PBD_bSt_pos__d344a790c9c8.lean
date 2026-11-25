-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_bSt_pos__d344a790c9c8
-- name    : P2M_Formalism_FourierDecayAlt_P_PBD_bSt_pos__d344a790c9c8
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:18.044988+00:00
-- url     : https://prove2.me/theorems/52df18f5-f07b-4a6e-b4c3-77f6690b6b1d
-- title:
--   P2 M Formalism Fourier Decay Alt P PBD b St pos  d344a790c9c8: P2 M Formalism Fourier Decay Alt P PBD b St pos  d344a790c9c8
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBD b St pos  d344a790c9c8 construction uses the P2 M Formalism Fourier Decay Alt P PBD b St pos  d344a790c9c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L50-L54

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

theorem P2M_Formalism_FourierDecayAlt_P_PBD_bSt_pos__d344a790c9c8 (κ : ℝ) (hκ : 0 < κ) (p : C.LPt) : 0 < D.bSt κ p := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBD».«bSt_pos'» := P2M_Formalism_FourierDecayAlt_P_PBD_bSt_pos__d344a790c9c8
