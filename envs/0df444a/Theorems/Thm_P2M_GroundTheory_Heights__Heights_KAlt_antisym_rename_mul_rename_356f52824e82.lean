-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_rename_mul_rename_356f52824e82
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_antisym_rename_mul_rename_356f52824e82
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:21.203225+00:00
-- url     : https://prove2.me/theorems/c1f774ba-1144-4541-b007-a0cf0504e19b
-- title:
--   P2 M Ground Theory Heights  Heights KAlt antisym rename mul rename 356f52824e82: P2 M Ground Theory Heights  Heights KAlt antisym rename mul rename 356f52824e82
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt antisym rename mul rename 356f52824e82 construction uses the P2 M Ground Theory Heights  Heights KAlt antisym rename mul rename 356f52824e82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L78-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.KAlt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r s : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KAlt_antisym_rename_mul_rename_356f52824e82 (α : Fin r → ℕ) (β : Fin s → ℕ) :
    antisym (rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β)) =
      ((r.factorial : ℚ) * s.factorial) • alternant (Sum.elim α β) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«antisym_rename_mul_rename» := P2M_GroundTheory_Heights__Heights_KAlt_antisym_rename_mul_rename_356f52824e82
