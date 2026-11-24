-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_whole_isArithVar_4efb22637fdb
-- name    : P2M_GroundTheory_Heights__Heights_whole_isArithVar_4efb22637fdb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:25.877645+00:00
-- url     : https://prove2.me/theorems/780b02ea-788b-4b1c-aea5-b3049a8fe12b
-- title:
--   P2 M Ground Theory Heights  Heights whole is Arith Var 4efb22637fdb: P2 M Ground Theory Heights  Heights whole is Arith Var 4efb22637fdb
-- statement:
--   The P2 M Ground Theory Heights  Heights whole is Arith Var 4efb22637fdb construction uses the P2 M Ground Theory Heights  Heights whole is Arith Var 4efb22637fdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L231-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L231-L233

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

theorem P2M_GroundTheory_Heights__Heights_whole_isArithVar_4efb22637fdb (N : ℕ) :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ N) (ArithVariety.whole fun _ : Unit ↦ N).ideal (N + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«whole_isArithVar» := P2M_GroundTheory_Heights__Heights_whole_isArithVar_4efb22637fdb
