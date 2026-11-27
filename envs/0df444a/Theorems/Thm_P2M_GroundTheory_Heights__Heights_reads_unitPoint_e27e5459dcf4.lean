-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_reads_unitPoint_e27e5459dcf4
-- name    : P2M_GroundTheory_Heights__Heights_reads_unitPoint_e27e5459dcf4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:35.519436+00:00
-- url     : https://prove2.me/theorems/4b1cd2a9-90d9-581f-8fe0-90003908399d
-- title:
--   P2 M Ground Theory Heights  Heights reads unit Point e27e5459dcf4: P2 M Ground Theory Heights  Heights reads unit Point e27e5459dcf4
-- statement:
--   The P2 M Ground Theory Heights  Heights reads unit Point e27e5459dcf4 construction uses the P2 M Ground Theory Heights  Heights reads unit Point e27e5459dcf4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L307-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L307-L332

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

theorem P2M_GroundTheory_Heights__Heights_reads_unitPoint_e27e5459dcf4 :
    (ArithVariety.whole fun _ : Unit ↦ 0).Reads unitPoint (fun _ ↦ 1) 1
      ((ArithVariety.whole fun _ : Unit ↦ 0).mkF (X ⟨(), 0⟩)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«reads_unitPoint» := P2M_GroundTheory_Heights__Heights_reads_unitPoint_e27e5459dcf4
