-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_wholePoint_isArithVar_12b9250c3e64
-- name    : P2M_GroundTheory_Heights__Heights_wholePoint_isArithVar_12b9250c3e64
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:33.190804+00:00
-- url     : https://prove2.me/theorems/c4c7578a-fe63-482b-8a92-5daff5a2f0ac
-- title:
--   P2 M Ground Theory Heights  Heights whole Point is Arith Var 12b9250c3e64: P2 M Ground Theory Heights  Heights whole Point is Arith Var 12b9250c3e64
-- statement:
--   The P2 M Ground Theory Heights  Heights whole Point is Arith Var 12b9250c3e64 construction uses the P2 M Ground Theory Heights  Heights whole Point is Arith Var 12b9250c3e64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L235-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L235-L239

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

theorem P2M_GroundTheory_Heights__Heights_wholePoint_isArithVar_12b9250c3e64 (N : ℕ) :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ N)
      (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ N) (wholePoint fun _ : Unit ↦ N)) (N + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«wholePoint_isArithVar» := P2M_GroundTheory_Heights__Heights_wholePoint_isArithVar_12b9250c3e64
