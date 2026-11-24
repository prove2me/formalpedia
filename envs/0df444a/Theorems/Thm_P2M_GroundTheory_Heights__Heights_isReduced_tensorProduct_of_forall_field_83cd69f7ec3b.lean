-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_forall_field_83cd69f7ec3b
-- name    : P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_forall_field_83cd69f7ec3b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:58.057868+00:00
-- url     : https://prove2.me/theorems/44c671d1-5cdf-4e13-8dac-49708794b194
-- title:
--   P2 M Ground Theory Heights  Heights is Reduced tensor Product of forall field 83cd69f7ec3b: P2 M Ground Theory Heights  Heights is Reduced tensor Product of forall field 83cd69f7ec3b
-- statement:
--   The P2 M Ground Theory Heights  Heights is Reduced tensor Product of forall field 83cd69f7ec3b construction uses the P2 M Ground Theory Heights  Heights is Reduced tensor Product of forall field 83cd69f7ec3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L14-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ReducedTensorPerfect.lean#L14-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ReducedTensorPerfect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open TensorProduct
noncomputable section
universe u
set_option synthInstance.maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_forall_field_83cd69f7ec3b {k : Type*} [Field k] (C : Type*) [CommRing C]
    [Algebra k C]
    (h : ∀ (E : Type u) [Field E] [Algebra k E] [Algebra.EssFiniteType k E], IsReduced (C ⊗[k] E))
    (A : Type u) [CommRing A] [Algebra k A] [IsReduced A] : IsReduced (C ⊗[k] A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isReduced_tensorProduct_of_forall_field» := P2M_GroundTheory_Heights__Heights_isReduced_tensorProduct_of_forall_field_83cd69f7ec3b
