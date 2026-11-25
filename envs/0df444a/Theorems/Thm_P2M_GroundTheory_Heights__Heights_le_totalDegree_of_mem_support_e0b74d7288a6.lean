-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_totalDegree_of_mem_support_e0b74d7288a6
-- name    : P2M_GroundTheory_Heights__Heights_le_totalDegree_of_mem_support_e0b74d7288a6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:39:16.524427+00:00
-- url     : https://prove2.me/theorems/60affcbc-cfba-4826-aa3d-97efefb19499
-- title:
--   P2 M Ground Theory Heights  Heights le total Degree of mem support e0b74d7288a6: P2 M Ground Theory Heights  Heights le total Degree of mem support e0b74d7288a6
-- statement:
--   The P2 M Ground Theory Heights  Heights le total Degree of mem support e0b74d7288a6 construction uses the P2 M Ground Theory Heights  Heights le total Degree of mem support e0b74d7288a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegreeRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_le_totalDegree_of_mem_support_e0b74d7288a6 {f : MvPolynomial (Coord n) ℚ} {m : Coord n →₀ ℕ}
    (hm : m ∈ f.support) (p : Coord n) : m p ≤ f.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«le_totalDegree_of_mem_support» := P2M_GroundTheory_Heights__Heights_le_totalDegree_of_mem_support_e0b74d7288a6
