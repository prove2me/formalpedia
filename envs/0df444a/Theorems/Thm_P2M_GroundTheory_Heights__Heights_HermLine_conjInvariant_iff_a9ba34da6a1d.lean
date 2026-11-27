-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_conjInvariant_iff_a9ba34da6a1d
-- name    : P2M_GroundTheory_Heights__Heights_HermLine_conjInvariant_iff_a9ba34da6a1d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:06.860478+00:00
-- url     : https://prove2.me/theorems/25ccb285-e4dc-5da5-b665-17a33042679d
-- title:
--   P2 M Ground Theory Heights  Heights Herm Line conj Invariant iff a9ba34da6a1d: P2 M Ground Theory Heights  Heights Herm Line conj Invariant iff a9ba34da6a1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Line conj Invariant iff a9ba34da6a1d construction uses the P2 M Ground Theory Heights  Heights Herm Line conj Invariant iff a9ba34da6a1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L20-L36

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

theorem P2M_GroundTheory_Heights__Heights_HermLine_conjInvariant_iff_a9ba34da6a1d (A : HermLine n) :
    A.ConjInvariant ↔ Geo.IsConjInvariantH A.toGeo := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermLine».«conjInvariant_iff» := P2M_GroundTheory_Heights__Heights_HermLine_conjInvariant_iff_a9ba34da6a1d
