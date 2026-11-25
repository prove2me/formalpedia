-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_max_zero_add_le_of_nonneg_b2974e2bf39a
-- name    : P2M_GroundTheory_Heights__Heights_LowerBound_max_zero_add_le_of_nonneg_b2974e2bf39a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:56.417006+00:00
-- url     : https://prove2.me/theorems/e6014810-2a18-4bdd-9b2e-b8f9e505ade3
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound max zero add le of nonneg b2974e2bf39a: P2 M Ground Theory Heights  Heights Lower Bound max zero add le of nonneg b2974e2bf39a
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound max zero add le of nonneg b2974e2bf39a construction uses the P2 M Ground Theory Heights  Heights Lower Bound max zero add le of nonneg b2974e2bf39a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PMeanCuspWeight.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PMeanCuspWeight.lean#L11-L12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PMeanCuspWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real MeasureTheory Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LowerBound_max_zero_add_le_of_nonneg_b2974e2bf39a {a b : ℝ} (hb : 0 ≤ b) : max 0 (a + b) ≤ max 0 a + b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBound».«max_zero_add_le_of_nonneg» := P2M_GroundTheory_Heights__Heights_LowerBound_max_zero_add_le_of_nonneg_b2974e2bf39a
