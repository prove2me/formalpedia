-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_sub_one_add_inv_sub_one_add_mul_eq_zero_9968b8cf05bb
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_sub_one_add_inv_sub_one_add_mul_eq_zero_9968b8cf05bb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:42.821654+00:00
-- url     : https://prove2.me/theorems/d7b6ceed-ffd0-4a0b-ac7b-d216b4f2e007
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling sub one add inv sub one add mul eq zero 9968b8cf05bb: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling sub on
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling sub one add inv sub one add mul eq zero 9968b8cf05bb construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling sub one add inv sub one add mul eq zero 9968b8cf05bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L67-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_sub_one_add_inv_sub_one_add_mul_eq_zero_9968b8cf05bb {E : Type*} [Field E] {u : E} (hu : u ≠ 0) :
    u - 1 + (u⁻¹ - 1) + (u - 1) * (u⁻¹ - 1) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«sub_one_add_inv_sub_one_add_mul_eq_zero» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_sub_one_add_inv_sub_one_add_mul_eq_zero_9968b8cf05bb
