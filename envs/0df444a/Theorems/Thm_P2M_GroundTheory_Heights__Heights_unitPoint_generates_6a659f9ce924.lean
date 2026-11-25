-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_unitPoint_generates_6a659f9ce924
-- name    : P2M_GroundTheory_Heights__Heights_unitPoint_generates_6a659f9ce924
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:08.943296+00:00
-- url     : https://prove2.me/theorems/db4122a8-6912-4f63-8585-2f3f8078d151
-- title:
--   P2 M Ground Theory Heights  Heights unit Point generates 6a659f9ce924: P2 M Ground Theory Heights  Heights unit Point generates 6a659f9ce924
-- statement:
--   The P2 M Ground Theory Heights  Heights unit Point generates 6a659f9ce924 construction uses the P2 M Ground Theory Heights  Heights unit Point generates 6a659f9ce924 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L334-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L334-L337

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

theorem P2M_GroundTheory_Heights__Heights_unitPoint_generates_6a659f9ce924 :
    (∀ j : Fin (0 + 1), (fun _ ↦ (1 : ℚ)) j ∈ Geo.chartLat (ι := blockIdx fun _ : Unit ↦ 0) unitPoint 0 1) ∧
      ArakelovGeometry.KH.GeneratesOn (ι := blockIdx fun _ : Unit ↦ 0) unitPoint 0 (fun _ : Fin (0 + 1) ↦ (1 : ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«unitPoint_generates» := P2M_GroundTheory_Heights__Heights_unitPoint_generates_6a659f9ce924
