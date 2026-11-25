-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockLine_conjInvariant_79da728bb562
-- name    : P2M_GroundTheory_Heights__Heights_blockLine_conjInvariant_79da728bb562
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:54.764585+00:00
-- url     : https://prove2.me/theorems/86c38f3c-4247-557f-a342-7b501c0514dc
-- title:
--   P2 M Ground Theory Heights  Heights block Line conj Invariant 79da728bb562: P2 M Ground Theory Heights  Heights block Line conj Invariant 79da728bb562
-- statement:
--   The P2 M Ground Theory Heights  Heights block Line conj Invariant 79da728bb562 construction uses the P2 M Ground Theory Heights  Heights block Line conj Invariant 79da728bb562 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L380-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L380-L381

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
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
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_blockLine_conjInvariant_79da728bb562 [Fintype ι] (k₀ : ι) : (blockLine n k₀).ConjInvariant := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockLine_conjInvariant» := P2M_GroundTheory_Heights__Heights_blockLine_conjInvariant_79da728bb562
