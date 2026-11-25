-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockReading_whole_00e04d17559a
-- name    : P2M_GroundTheory_Heights__Heights_blockReading_whole_00e04d17559a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:38.211135+00:00
-- url     : https://prove2.me/theorems/9ac95ec4-4412-49af-94ac-91340ab5716a
-- title:
--   P2 M Ground Theory Heights  Heights block Reading whole 00e04d17559a: P2 M Ground Theory Heights  Heights block Reading whole 00e04d17559a
-- statement:
--   The P2 M Ground Theory Heights  Heights block Reading whole 00e04d17559a construction uses the P2 M Ground Theory Heights  Heights block Reading whole 00e04d17559a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L206-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L206-L219

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

theorem P2M_GroundTheory_Heights__Heights_blockReading_whole_00e04d17559a (D : AddBlockData (ArithVariety.whole n)) :
    D.BlockReading (wholePoint n) D.elt := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockReading_whole» := P2M_GroundTheory_Heights__Heights_blockReading_whole_00e04d17559a
