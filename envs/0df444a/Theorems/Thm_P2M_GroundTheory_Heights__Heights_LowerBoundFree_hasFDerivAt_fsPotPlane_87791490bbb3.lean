-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_fsPotPlane_87791490bbb3
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_fsPotPlane_87791490bbb3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:01.534608+00:00
-- url     : https://prove2.me/theorems/d29dec92-5489-4dba-99ce-8bde5048ab04
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free has FDeriv At fs Pot Plane 87791490bbb3: P2 M Ground Theory Heights  Heights Lower Bound Free has FDeriv At fs Pot Plane 87791490bbb3
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free has FDeriv At fs Pot Plane 87791490bbb3 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free has FDeriv At fs Pot Plane 87791490bbb3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L11-L22

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_fsPotPlane_87791490bbb3 (z : ℂ) :
    HasFDerivAt fsPotPlane ((1 + ‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«hasFDerivAt_fsPotPlane» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_fsPotPlane_87791490bbb3
