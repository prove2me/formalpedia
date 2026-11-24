-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_laplacian_fsPotPlane_429c59d53f91
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_laplacian_fsPotPlane_429c59d53f91
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:18.625553+00:00
-- url     : https://prove2.me/theorems/0fdb8eca-48d4-42e7-b98d-e67671c0131b
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free laplacian fs Pot Plane 429c59d53f91: P2 M Ground Theory Heights  Heights Lower Bound Free laplacian fs Pot Plane 429c59d53f91
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free laplacian fs Pot Plane 429c59d53f91 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free laplacian fs Pot Plane 429c59d53f91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L65-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L65-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian
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
open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_laplacian_fsPotPlane_429c59d53f91 (y : ℂ) : Δ fsPotPlane y = 2 / (1 + ‖y‖ ^ 2) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«laplacian_fsPotPlane» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_laplacian_fsPotPlane_429c59d53f91
