-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_permSign_inv__c2e72e289cc8
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_permSign_inv__c2e72e289cc8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:48.033819+00:00
-- url     : https://prove2.me/theorems/46fdfab3-fbc6-4e2c-b1f4-b1572d0238e3
-- title:
--   P2 M Ground Theory Heights  Heights KAlt perm Sign inv  c2e72e289cc8: P2 M Ground Theory Heights  Heights KAlt perm Sign inv  c2e72e289cc8
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt perm Sign inv  c2e72e289cc8 construction uses the P2 M Ground Theory Heights  Heights KAlt perm Sign inv  c2e72e289cc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L36-L37

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_permSign_inv__c2e72e289cc8 (a : Equiv.Perm ι) : sgnP a⁻¹ = sgnP a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«permSign_inv₂» := P2M_GroundTheory_Heights__Heights_KAlt_permSign_inv__c2e72e289cc8
