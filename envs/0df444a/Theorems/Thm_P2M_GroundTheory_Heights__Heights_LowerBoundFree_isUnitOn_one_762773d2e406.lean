-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitOn_one_762773d2e406
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitOn_one_762773d2e406
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:50.537797+00:00
-- url     : https://prove2.me/theorems/00b72e41-b3f1-4406-853c-ec515ff7f7d7
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Unit On one 762773d2e406: P2 M Ground Theory Heights  Heights Lower Bound Free is Unit On one 762773d2e406
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Unit On one 762773d2e406 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Unit On one 762773d2e406 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L70-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitOn_one_762773d2e406 (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (f : Ω) : IsUnitOn y c f 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isUnitOn_one» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isUnitOn_one_762773d2e406
