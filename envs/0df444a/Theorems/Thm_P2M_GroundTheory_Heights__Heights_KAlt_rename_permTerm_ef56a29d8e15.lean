-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_rename_permTerm_ef56a29d8e15
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_rename_permTerm_ef56a29d8e15
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:57.055711+00:00
-- url     : https://prove2.me/theorems/f3864779-a707-4164-a637-8011601f504b
-- title:
--   P2 M Ground Theory Heights  Heights KAlt rename perm Term ef56a29d8e15: P2 M Ground Theory Heights  Heights KAlt rename perm Term ef56a29d8e15
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt rename perm Term ef56a29d8e15 construction uses the P2 M Ground Theory Heights  Heights KAlt rename perm Term ef56a29d8e15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L29-L31

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_KAlt_rename_permTerm_ef56a29d8e15 (e : ι → ℕ) (w π : Equiv.Perm ι) :
    rename w (permTerm e π) = permTerm e (w * π) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«rename_permTerm» := P2M_GroundTheory_Heights__Heights_KAlt_rename_permTerm_ef56a29d8e15
