-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_eq_sum_314cba1d0338
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_antisym_eq_sum_314cba1d0338
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:20.452371+00:00
-- url     : https://prove2.me/theorems/9f9d6227-67fd-4a88-9818-9377cf68f7a9
-- title:
--   P2 M Ground Theory Heights  Heights KAlt antisym eq sum 314cba1d0338: P2 M Ground Theory Heights  Heights KAlt antisym eq sum 314cba1d0338
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt antisym eq sum 314cba1d0338 construction uses the P2 M Ground Theory Heights  Heights KAlt antisym eq sum 314cba1d0338 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean#L22-L26

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_antisym_eq_sum_314cba1d0338 (H : MvPolynomial ι ℚ) : antisym H = ∑ w, sgnP w * rename w H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«antisym_eq_sum» := P2M_GroundTheory_Heights__Heights_KAlt_antisym_eq_sum_314cba1d0338
