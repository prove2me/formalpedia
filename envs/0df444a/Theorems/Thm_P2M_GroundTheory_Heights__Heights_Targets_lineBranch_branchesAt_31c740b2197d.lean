-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_lineBranch_branchesAt_31c740b2197d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_lineBranch_branchesAt_31c740b2197d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:41:03.188397+00:00
-- url     : https://prove2.me/theorems/e036b459-7d1d-4476-a048-f225ac222b57
-- title:
--   P2 M Ground Theory Heights  Heights Targets line Branch branches At 31c740b2197d: P2 M Ground Theory Heights  Heights Targets line Branch branches At 31c740b2197d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets line Branch branches At 31c740b2197d construction uses the P2 M Ground Theory Heights  Heights Targets line Branch branches At 31c740b2197d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeBranchLength.lean#L137-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeBranchLength.lean#L137-L156

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

theorem P2M_GroundTheory_Heights__Heights_Targets_lineBranch_branchesAt_31c740b2197d :
    ConeBranchesAt (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) (Ideal.span {X ⟨(), 0⟩}) (d := 1) ptZeroOne
      (fun _ : Fin 1 => lineBranch) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«lineBranch_branchesAt» := P2M_GroundTheory_Heights__Heights_Targets_lineBranch_branchesAt_31c740b2197d
