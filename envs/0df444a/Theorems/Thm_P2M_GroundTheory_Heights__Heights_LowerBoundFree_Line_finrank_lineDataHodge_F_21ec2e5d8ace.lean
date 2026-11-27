-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_finrank_lineDataHodge_F_21ec2e5d8ace
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_finrank_lineDataHodge_F_21ec2e5d8ace
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:30.283577+00:00
-- url     : https://prove2.me/theorems/25187e85-bf28-4bb1-8e64-653062ad3574
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line finrank line Data Hodge F 21ec2e5d8ace: P2 M Ground Theory Heights  Heights Lower Bound Free Line finrank line Data Hodge F 21ec2e5d8ace
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line finrank line Data Hodge F 21ec2e5d8ace construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line finrank line Data Hodge F 21ec2e5d8ace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/DataHodge.lean#L48-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/DataHodge.lean#L48-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_Example
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_DataHodge
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
open GroundTheory.Heights₂.Heights.LowerBoundFree.Line

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_finrank_lineDataHodge_F_21ec2e5d8ace (II : IntersectionSystem) (hII) :
    Module.finrank Ω ((lineDataHodge II hII).F ()) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«finrank_lineDataHodge_F» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_finrank_lineDataHodge_F_21ec2e5d8ace
