-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isSupSmallBlock_one_ce57b19d901a
-- name    : P2M_GroundTheory_Heights__Heights_isSupSmallBlock_one_ce57b19d901a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:21.826971+00:00
-- url     : https://prove2.me/theorems/69e6aa3e-500a-4b89-8b40-1afc4bf7b40a
-- title:
--   P2 M Ground Theory Heights  Heights is Sup Small Block one ce57b19d901a: P2 M Ground Theory Heights  Heights is Sup Small Block one ce57b19d901a
-- statement:
--   The P2 M Ground Theory Heights  Heights is Sup Small Block one ce57b19d901a construction uses the P2 M Ground Theory Heights  Heights is Sup Small Block one ce57b19d901a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L436-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L436-L462

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

theorem P2M_GroundTheory_Heights__Heights_isSupSmallBlock_one_ce57b19d901a {κ : Type} [Fintype κ] [DecidableEq κ] {n' : κ → ℕ} {Ω : Type} [Field Ω]
    [CharZero Ω] (y : Coord n' → Ω) (k₀ : κ) (A : Geo.HermLine (blockIdx n')) :
    (1 : Ω) ∈ Geo.secM (ι := blockIdx n') y (Pi.single k₀ 0) ∧ IsSupSmallBlock y k₀ A 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isSupSmallBlock_one» := P2M_GroundTheory_Heights__Heights_isSupSmallBlock_one_ce57b19d901a
