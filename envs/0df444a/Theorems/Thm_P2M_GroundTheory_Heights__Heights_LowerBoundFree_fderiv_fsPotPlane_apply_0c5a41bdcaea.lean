-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_fderiv_fsPotPlane_apply_0c5a41bdcaea
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_fderiv_fsPotPlane_apply_0c5a41bdcaea
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:51.603096+00:00
-- url     : https://prove2.me/theorems/a134bb98-643a-47ee-b82c-6d10e7a997df
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free fderiv fs Pot Plane apply 0c5a41bdcaea: P2 M Ground Theory Heights  Heights Lower Bound Free fderiv fs Pot Plane apply 0c5a41bdcaea
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free fderiv fs Pot Plane apply 0c5a41bdcaea construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free fderiv fs Pot Plane apply 0c5a41bdcaea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L24-L27

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_fderiv_fsPotPlane_apply_0c5a41bdcaea (z e : ℂ) :
    fderiv ℝ fsPotPlane z e = (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«fderiv_fsPotPlane_apply» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_fderiv_fsPotPlane_apply_0c5a41bdcaea
