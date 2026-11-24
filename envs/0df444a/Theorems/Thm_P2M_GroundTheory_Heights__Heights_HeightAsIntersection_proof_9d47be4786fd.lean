-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightAsIntersection_proof_9d47be4786fd
-- name    : P2M_GroundTheory_Heights__Heights_HeightAsIntersection_proof_9d47be4786fd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:27.678319+00:00
-- url     : https://prove2.me/theorems/b0a20c63-ada7-45d3-b046-582eca2dbf23
-- title:
--   P2 M Ground Theory Heights  Heights Height As Intersection proof 9d47be4786fd: P2 M Ground Theory Heights  Heights Height As Intersection proof 9d47be4786fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Height As Intersection proof 9d47be4786fd construction uses the P2 M Ground Theory Heights  Heights Height As Intersection proof 9d47be4786fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/Height.lean#L64-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/Height.lean#L64-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
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
open ReciprocityTheory.ChartRestriction.G NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_HeightAsIntersection_proof_9d47be4786fd (h₁ : OrbitCurve.Statement) (h₂ : OrbitDegree.Statement)
    (h₃ : HeightRecR.Statement) : HeightAsIntersection.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HeightAsIntersection».«proof» := P2M_GroundTheory_Heights__Heights_HeightAsIntersection_proof_9d47be4786fd
