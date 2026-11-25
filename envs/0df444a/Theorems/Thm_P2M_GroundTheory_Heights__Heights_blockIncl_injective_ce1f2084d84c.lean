-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockIncl_injective_ce1f2084d84c
-- name    : P2M_GroundTheory_Heights__Heights_blockIncl_injective_ce1f2084d84c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:38.103148+00:00
-- url     : https://prove2.me/theorems/28142a73-040c-4af4-ac6e-5392291ee243
-- title:
--   P2 M Ground Theory Heights  Heights block Incl injective ce1f2084d84c: P2 M Ground Theory Heights  Heights block Incl injective ce1f2084d84c
-- statement:
--   The P2 M Ground Theory Heights  Heights block Incl injective ce1f2084d84c construction uses the P2 M Ground Theory Heights  Heights block Incl injective ce1f2084d84c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VarsSubsetRangeBlockIncl.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VarsSubsetRangeBlockIncl.lean#L14-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VarsSubsetRangeBlockIncl
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_blockIncl_injective_ce1f2084d84c (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockIncl_injective» := P2M_GroundTheory_Heights__Heights_blockIncl_injective_ce1f2084d84c
