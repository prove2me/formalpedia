-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply__260edcdff289
-- name    : P2M_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply__260edcdff289
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:17.135202+00:00
-- url     : https://prove2.me/theorems/4347d192-df60-4bce-8f6a-2bbc747124b8
-- title:
--   P2 M Ground Theory Automorphic Restricted Tensor eq zero of forall apply  260edcdff289: P2 M Ground Theory Automorphic Restricted Tensor eq zero of forall apply  260edcdff289
-- statement:
--   The P2 M Ground Theory Automorphic Restricted Tensor eq zero of forall apply  260edcdff289 construction uses the P2 M Ground Theory Automorphic Restricted Tensor eq zero of forall apply  260edcdff289 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L44-L54

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

theorem P2M_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply__260edcdff289 {ρ : Representation ℂ M V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    {l : Dual ℂ V} (h : ∀ m, l (ρ m v) = 0) : l = 0 := by sorry

alias «GroundTheory».«Automorphic».«RestrictedTensor».«eq_zero_of_forall_apply'» := P2M_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply__260edcdff289
