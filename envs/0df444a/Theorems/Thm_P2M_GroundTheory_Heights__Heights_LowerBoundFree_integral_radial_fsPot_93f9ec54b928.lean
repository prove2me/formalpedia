-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_integral_radial_fsPot_93f9ec54b928
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_integral_radial_fsPot_93f9ec54b928
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:13.202846+00:00
-- url     : https://prove2.me/theorems/3b6c7c44-cccd-4370-803f-b73ad2334184
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free integral radial fs Pot 93f9ec54b928: P2 M Ground Theory Heights  Heights Lower Bound Free integral radial fs Pot 93f9ec54b928
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free integral radial fs Pot 93f9ec54b928 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free integral radial fs Pot 93f9ec54b928 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L86-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L86-L105

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_integral_radial_fsPot_93f9ec54b928 :
    ∫ s in Ioi (0 : ℝ), s ^ (2 - 1) • (2 / (1 + s ^ 2) ^ 2) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«integral_radial_fsPot» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_integral_radial_fsPot_93f9ec54b928
