-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mCoordIdeal_unitPoint_4af6af0c0629
-- name    : P2M_GroundTheory_Heights__Heights_mCoordIdeal_unitPoint_4af6af0c0629
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:54:45.695552+00:00
-- url     : https://prove2.me/theorems/08210e14-05c1-5801-9d4e-e469ef65313a
-- title:
--   P2 M Ground Theory Heights  Heights m Coord Ideal unit Point 4af6af0c0629: P2 M Ground Theory Heights  Heights m Coord Ideal unit Point 4af6af0c0629
-- statement:
--   The P2 M Ground Theory Heights  Heights m Coord Ideal unit Point 4af6af0c0629 construction uses the P2 M Ground Theory Heights  Heights m Coord Ideal unit Point 4af6af0c0629 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L243-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L243-L257

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

theorem P2M_GroundTheory_Heights__Heights_mCoordIdeal_unitPoint_4af6af0c0629 :
    Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mCoordIdeal_unitPoint» := P2M_GroundTheory_Heights__Heights_mCoordIdeal_unitPoint_4af6af0c0629
