-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul_self__1c23ec0bec6d
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul_self__1c23ec0bec6d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:55.646437+00:00
-- url     : https://prove2.me/theorems/30cc9756-2c17-4c44-bdb3-984a6747e17f
-- title:
--   P2 M Ground Theory Heights  Heights KAlt perm Sign mul self  1c23ec0bec6d: P2 M Ground Theory Heights  Heights KAlt perm Sign mul self  1c23ec0bec6d
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt perm Sign mul self  1c23ec0bec6d construction uses the P2 M Ground Theory Heights  Heights KAlt perm Sign mul self  1c23ec0bec6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L39-L42

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul_self__1c23ec0bec6d (a : Equiv.Perm ι) : sgnP a * sgnP a = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«permSign_mul_self₂» := P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul_self__1c23ec0bec6d
