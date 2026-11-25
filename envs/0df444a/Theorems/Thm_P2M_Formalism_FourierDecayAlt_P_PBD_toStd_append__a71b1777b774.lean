-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_toStd_append__a71b1777b774
-- name    : P2M_Formalism_FourierDecayAlt_P_PBD_toStd_append__a71b1777b774
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:18.722815+00:00
-- url     : https://prove2.me/theorems/f63bcc3f-6144-4845-a45d-2912d20f5df0
-- title:
--   P2 M Formalism Fourier Decay Alt P PBD to Std append  a71b1777b774: P2 M Formalism Fourier Decay Alt P PBD to Std append  a71b1777b774
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBD to Std append  a71b1777b774 construction uses the P2 M Formalism Fourier Decay Alt P PBD to Std append  a71b1777b774 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L10-L16

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

theorem P2M_Formalism_FourierDecayAlt_P_PBD_toStd_append__a71b1777b774 (r : ℕ) (g : ℝ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(1, c)]) = D.toStd r g b h ++
      [(1, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) ((1 : ℕ) : ℤ) : ℝ) : ℂ) * c)]
  := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBD».«toStd_append'» := P2M_Formalism_FourierDecayAlt_P_PBD_toStd_append__a71b1777b774
