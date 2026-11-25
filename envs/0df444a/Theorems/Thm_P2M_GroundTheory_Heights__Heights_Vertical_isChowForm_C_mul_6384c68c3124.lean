-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_isChowForm_C_mul_6384c68c3124
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_isChowForm_C_mul_6384c68c3124
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:25.816052+00:00
-- url     : https://prove2.me/theorems/584ebe12-d5eb-484c-a603-c54762963dde
-- title:
--   P2 M Ground Theory Heights  Heights Vertical is Chow Form C mul 6384c68c3124: P2 M Ground Theory Heights  Heights Vertical is Chow Form C mul 6384c68c3124
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical is Chow Form C mul 6384c68c3124 construction uses the P2 M Ground Theory Heights  Heights Vertical is Chow Form C mul 6384c68c3124 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/IsChowFormCMul.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/IsChowFormCMul.lean#L12-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IsChowFormCMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_isChowForm_C_mul_6384c68c3124 {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«isChowForm_C_mul» := P2M_GroundTheory_Heights__Heights_Vertical_isChowForm_C_mul_6384c68c3124
