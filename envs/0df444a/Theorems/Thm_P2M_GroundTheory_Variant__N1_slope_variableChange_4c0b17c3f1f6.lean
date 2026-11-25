-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_slope_variableChange_4c0b17c3f1f6
-- name    : P2M_GroundTheory_Variant__N1_slope_variableChange_4c0b17c3f1f6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:49.977483+00:00
-- url     : https://prove2.me/theorems/dd8b4277-5611-51c0-9b88-503d7caa1ea2
-- title:
--   P2 M Ground Theory Variant  N1 slope variable Change 4c0b17c3f1f6: P2 M Ground Theory Variant  N1 slope variable Change 4c0b17c3f1f6
-- statement:
--   The P2 M Ground Theory Variant  N1 slope variable Change 4c0b17c3f1f6 construction uses the P2 M Ground Theory Variant  N1 slope variable Change 4c0b17c3f1f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/SlopeVcCountableNeighbourhoods.lean#L13-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/SlopeVcCountableNeighbourhoods.lean#L13-L59

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_SlopeVcCountableNeighbourhoods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open WeierstrassCurve

theorem P2M_GroundTheory_Variant__N1_slope_variableChange_4c0b17c3f1f6 {F : Type*} [Field F] (C : WeierstrassCurve.VariableChange F)
    (W : WeierstrassCurve F) [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂) =
      ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by sorry

alias «GroundTheory».«Variant₂».«N1».«slope_variableChange» := P2M_GroundTheory_Variant__N1_slope_variableChange_4c0b17c3f1f6
