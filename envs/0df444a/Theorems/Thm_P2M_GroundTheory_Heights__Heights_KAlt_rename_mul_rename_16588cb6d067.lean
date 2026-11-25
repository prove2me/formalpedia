-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_rename_mul_rename_16588cb6d067
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_rename_mul_rename_16588cb6d067
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:46.13792+00:00
-- url     : https://prove2.me/theorems/d86801f6-4b36-561a-8527-b07484e05ce2
-- title:
--   P2 M Ground Theory Heights  Heights KAlt rename mul rename 16588cb6d067: P2 M Ground Theory Heights  Heights KAlt rename mul rename 16588cb6d067
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt rename mul rename 16588cb6d067 construction uses the P2 M Ground Theory Heights  Heights KAlt rename mul rename 16588cb6d067 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L66-L76

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_rename_mul_rename_16588cb6d067 (α : Fin r → ℕ) (β : Fin s → ℕ) :
    rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β) =
      ∑ σ : Equiv.Perm (Fin r), ∑ τ : Equiv.Perm (Fin s),
        sgnP (Equiv.Perm.sumCongr σ τ) * permTerm (Sum.elim α β) (Equiv.Perm.sumCongr σ τ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«rename_mul_rename» := P2M_GroundTheory_Heights__Heights_KAlt_rename_mul_rename_16588cb6d067
