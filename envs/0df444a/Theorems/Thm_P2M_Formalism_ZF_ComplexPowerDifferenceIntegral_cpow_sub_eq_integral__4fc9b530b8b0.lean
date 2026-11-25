-- Prove2me | Theorems.Thm_P2M_Formalism_ZF_ComplexPowerDifferenceIntegral_cpow_sub_eq_integral__4fc9b530b8b0
-- name    : P2M_Formalism_ZF_ComplexPowerDifferenceIntegral_cpow_sub_eq_integral__4fc9b530b8b0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:55.967539+00:00
-- url     : https://prove2.me/theorems/d5b75fe9-18a6-4697-ba70-9d90ec6c69f6
-- title:
--   P2 M Formalism ZF Complex Power Difference Integral cpow sub eq integral  4fc9b530b8b0: P2 M Formalism ZF Complex Power Difference Integral cpow sub eq integral  4fc9b530b8b0
-- statement:
--   The P2 M Formalism ZF Complex Power Difference Integral cpow sub eq integral  4fc9b530b8b0 construction uses the P2 M Formalism ZF Complex Power Difference Integral cpow sub eq integral  4fc9b530b8b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormCpowSubLePoint.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormCpowSubLePoint.lean#L11-L20

import Mathlib
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral

theorem P2M_Formalism_ZF_ComplexPowerDifferenceIntegral_cpow_sub_eq_integral__4fc9b530b8b0 {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {s : ℂ} (hs : s ≠ 0) :
    (x : ℂ) ^ (-s) - (y : ℂ) ^ (-s) = s * ∫ t in x..y, (t : ℂ) ^ (-s - 1) := by sorry

alias «Formalism».«ZF».«ComplexPowerDifferenceIntegral».«cpow_sub_eq_integral'» := P2M_Formalism_ZF_ComplexPowerDifferenceIntegral_cpow_sub_eq_integral__4fc9b530b8b0
