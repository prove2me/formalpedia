-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul__3be578588ef6
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul__3be578588ef6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:09.341007+00:00
-- url     : https://prove2.me/theorems/51839a63-2cba-41a0-af50-d410536c2f65
-- title:
--   P2 M Ground Theory Heights  Heights KAlt perm Sign mul  3be578588ef6: P2 M Ground Theory Heights  Heights KAlt perm Sign mul  3be578588ef6
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt perm Sign mul  3be578588ef6 construction uses the P2 M Ground Theory Heights  Heights KAlt perm Sign mul  3be578588ef6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L33-L34

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul__3be578588ef6 (a b : Equiv.Perm ι) : sgnP (a * b) = sgnP a * sgnP b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«permSign_mul₂» := P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul__3be578588ef6
