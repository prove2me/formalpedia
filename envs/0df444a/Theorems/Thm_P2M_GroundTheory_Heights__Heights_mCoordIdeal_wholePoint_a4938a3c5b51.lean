-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mCoordIdeal_wholePoint_a4938a3c5b51
-- name    : P2M_GroundTheory_Heights__Heights_mCoordIdeal_wholePoint_a4938a3c5b51
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:59.819125+00:00
-- url     : https://prove2.me/theorems/301d3f1c-d811-40ee-9881-2ce235d4bc60
-- title:
--   P2 M Ground Theory Heights  Heights m Coord Ideal whole Point a4938a3c5b51: P2 M Ground Theory Heights  Heights m Coord Ideal whole Point a4938a3c5b51
-- statement:
--   The P2 M Ground Theory Heights  Heights m Coord Ideal whole Point a4938a3c5b51 construction uses the P2 M Ground Theory Heights  Heights m Coord Ideal whole Point a4938a3c5b51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L199-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L199-L204

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

theorem P2M_GroundTheory_Heights__Heights_mCoordIdeal_wholePoint_a4938a3c5b51 :
    Geo.mCoordIdeal (ι := blockIdx n) (wholePoint n) = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mCoordIdeal_wholePoint» := P2M_GroundTheory_Heights__Heights_mCoordIdeal_wholePoint_a4938a3c5b51
