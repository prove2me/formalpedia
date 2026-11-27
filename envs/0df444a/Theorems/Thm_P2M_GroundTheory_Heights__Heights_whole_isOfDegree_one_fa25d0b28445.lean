-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_whole_isOfDegree_one_fa25d0b28445
-- name    : P2M_GroundTheory_Heights__Heights_whole_isOfDegree_one_fa25d0b28445
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:59.506145+00:00
-- url     : https://prove2.me/theorems/c20d0572-205c-5216-846a-f4fe57e69bf2
-- title:
--   P2 M Ground Theory Heights  Heights whole is Of Degree one fa25d0b28445: P2 M Ground Theory Heights  Heights whole is Of Degree one fa25d0b28445
-- statement:
--   The P2 M Ground Theory Heights  Heights whole is Of Degree one fa25d0b28445 construction uses the P2 M Ground Theory Heights  Heights whole is Of Degree one fa25d0b28445 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L476-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L476-L477

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

theorem P2M_GroundTheory_Heights__Heights_whole_isOfDegree_one_fa25d0b28445 : (ArithVariety.whole n).IsOfDegree 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«whole_isOfDegree_one» := P2M_GroundTheory_Heights__Heights_whole_isOfDegree_one_fa25d0b28445
