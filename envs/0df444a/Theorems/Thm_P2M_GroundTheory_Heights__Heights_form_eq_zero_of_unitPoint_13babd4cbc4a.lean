-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_form_eq_zero_of_unitPoint_13babd4cbc4a
-- name    : P2M_GroundTheory_Heights__Heights_form_eq_zero_of_unitPoint_13babd4cbc4a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:39.633096+00:00
-- url     : https://prove2.me/theorems/b8b5a2a5-e312-4208-97ca-239417630b35
-- title:
--   P2 M Ground Theory Heights  Heights form eq zero of unit Point 13babd4cbc4a: P2 M Ground Theory Heights  Heights form eq zero of unit Point 13babd4cbc4a
-- statement:
--   The P2 M Ground Theory Heights  Heights form eq zero of unit Point 13babd4cbc4a construction uses the P2 M Ground Theory Heights  Heights form eq zero of unit Point 13babd4cbc4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L282-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L282-L305

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

theorem P2M_GroundTheory_Heights__Heights_form_eq_zero_of_unitPoint_13babd4cbc4a {f : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ} {δ : Unit → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ 0) f δ) (h : aeval unitPoint f = 0) : f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«form_eq_zero_of_unitPoint» := P2M_GroundTheory_Heights__Heights_form_eq_zero_of_unitPoint_13babd4cbc4a
