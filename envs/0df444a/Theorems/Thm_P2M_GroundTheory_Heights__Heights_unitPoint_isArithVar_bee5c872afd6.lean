-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_unitPoint_isArithVar_bee5c872afd6
-- name    : P2M_GroundTheory_Heights__Heights_unitPoint_isArithVar_bee5c872afd6
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:17.987617+00:00
-- url     : https://prove2.me/theorems/7858ce35-b4e8-4e02-ad2b-d1b70c53b1e9
-- title:
--   P2 M Ground Theory Heights  Heights unit Point is Arith Var bee5c872afd6: P2 M Ground Theory Heights  Heights unit Point is Arith Var bee5c872afd6
-- statement:
--   The P2 M Ground Theory Heights  Heights unit Point is Arith Var bee5c872afd6 construction uses the P2 M Ground Theory Heights  Heights unit Point is Arith Var bee5c872afd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L259-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L259-L263

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

theorem P2M_GroundTheory_Heights__Heights_unitPoint_isArithVar_bee5c872afd6 :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ 0)
      (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«unitPoint_isArithVar» := P2M_GroundTheory_Heights__Heights_unitPoint_isArithVar_bee5c872afd6
