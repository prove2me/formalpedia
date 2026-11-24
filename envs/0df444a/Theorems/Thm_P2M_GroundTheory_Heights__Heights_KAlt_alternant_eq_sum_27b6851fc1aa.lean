-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_alternant_eq_sum_27b6851fc1aa
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_alternant_eq_sum_27b6851fc1aa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:18.638719+00:00
-- url     : https://prove2.me/theorems/64ccb851-cfff-4427-b53a-508664d76a68
-- title:
--   P2 M Ground Theory Heights  Heights KAlt alternant eq sum 27b6851fc1aa: P2 M Ground Theory Heights  Heights KAlt alternant eq sum 27b6851fc1aa
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt alternant eq sum 27b6851fc1aa construction uses the P2 M Ground Theory Heights  Heights KAlt alternant eq sum 27b6851fc1aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L19-L20

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_alternant_eq_sum_27b6851fc1aa (e : ι → ℕ) : alternant e = ∑ π, sgnP π * permTerm e π := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«alternant_eq_sum» := P2M_GroundTheory_Heights__Heights_KAlt_alternant_eq_sum_27b6851fc1aa
