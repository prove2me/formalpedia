-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_sign_mul_bb5e29a75a0d
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_antisym_sign_mul_bb5e29a75a0d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:33.301543+00:00
-- url     : https://prove2.me/theorems/6256cfde-3db5-564a-a7d8-ed1fe3220a55
-- title:
--   P2 M Ground Theory Heights  Heights KAlt antisym sign mul bb5e29a75a0d: P2 M Ground Theory Heights  Heights KAlt antisym sign mul bb5e29a75a0d
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt antisym sign mul bb5e29a75a0d construction uses the P2 M Ground Theory Heights  Heights KAlt antisym sign mul bb5e29a75a0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L58-L62

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_antisym_sign_mul_bb5e29a75a0d (a : Equiv.Perm ι) (p : MvPolynomial ι ℚ) :
    antisym (sgnP a * p) = sgnP a * antisym p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«antisym_sign_mul» := P2M_GroundTheory_Heights__Heights_KAlt_antisym_sign_mul_bb5e29a75a0d
