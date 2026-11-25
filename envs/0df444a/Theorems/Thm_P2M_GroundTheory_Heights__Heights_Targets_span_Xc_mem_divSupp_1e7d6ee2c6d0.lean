-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_span_Xc_mem_divSupp_1e7d6ee2c6d0
-- name    : P2M_GroundTheory_Heights__Heights_Targets_span_Xc_mem_divSupp_1e7d6ee2c6d0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:56.910771+00:00
-- url     : https://prove2.me/theorems/5bd574ce-6749-516b-a61b-7ad24da353a2
-- title:
--   P2 M Ground Theory Heights  Heights Targets span Xc mem div Supp 1e7d6ee2c6d0: P2 M Ground Theory Heights  Heights Targets span Xc mem div Supp 1e7d6ee2c6d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets span Xc mem div Supp 1e7d6ee2c6d0 construction uses the P2 M Ground Theory Heights  Heights Targets span Xc mem div Supp 1e7d6ee2c6d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeBranchLength.lean#L123-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeBranchLength.lean#L123-L135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeBranchLength
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter

theorem P2M_GroundTheory_Heights__Heights_Targets_span_Xc_mem_divSupp_1e7d6ee2c6d0 :
    (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«span_Xc_mem_divSupp» := P2M_GroundTheory_Heights__Heights_Targets_span_Xc_mem_divSupp_1e7d6ee2c6d0
