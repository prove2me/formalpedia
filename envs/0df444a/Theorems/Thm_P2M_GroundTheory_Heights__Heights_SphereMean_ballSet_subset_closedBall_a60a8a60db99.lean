-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_subset_closedBall_a60a8a60db99
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_subset_closedBall_a60a8a60db99
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:16.261695+00:00
-- url     : https://prove2.me/theorems/cbcc0772-f687-4f8d-9706-fbc035f86a99
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean ball Set subset closed Ball a60a8a60db99: P2 M Ground Theory Heights  Heights Sphere Mean ball Set subset closed Ball a60a8a60db99
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean ball Set subset closed Ball a60a8a60db99 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean ball Set subset closed Ball a60a8a60db99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L87-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_subset_closedBall_a60a8a60db99 (n : ℕ) : ballSet n 1 ⊆ Metric.closedBall 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«ballSet_subset_closedBall» := P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_subset_closedBall_a60a8a60db99
