-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_flat_of_eq_zero_of_intCast_mul_4de2fa557ad9
-- name    : P2M_GroundTheory_Heights__Heights_Model_flat_of_eq_zero_of_intCast_mul_4de2fa557ad9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:31:43.625191+00:00
-- url     : https://prove2.me/theorems/d1c73d01-3836-45c1-a6a7-dff4916e8a69
-- title:
--   P2 M Ground Theory Heights  Heights Model flat of eq zero of int Cast mul 4de2fa557ad9: P2 M Ground Theory Heights  Heights Model flat of eq zero of int Cast mul 4de2fa557ad9
-- statement:
--   The P2 M Ground Theory Heights  Heights Model flat of eq zero of int Cast mul 4de2fa557ad9 construction uses the P2 M Ground Theory Heights  Heights Model flat of eq zero of int Cast mul 4de2fa557ad9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L94-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L94-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_flat_of_eq_zero_of_intCast_mul_4de2fa557ad9 {Y : Scheme.{0}} (g : Y ⟶ SpecZ)
    (hT : ∀ (V : Y.Opens) (n : ℤ) (s : Γ(Y, V)), n ≠ 0 → (n : Γ(Y, V)) * s = 0 → s = 0) :
    Flat g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«flat_of_eq_zero_of_intCast_mul» := P2M_GroundTheory_Heights__Heights_Model_flat_of_eq_zero_of_intCast_mul_4de2fa557ad9
