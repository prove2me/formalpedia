-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isSmallH_one_wholePoint_586e1e8d0445
-- name    : P2M_GroundTheory_Heights__Heights_isSmallH_one_wholePoint_586e1e8d0445
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:00.766639+00:00
-- url     : https://prove2.me/theorems/cdff2e8e-8745-47b4-ba0e-fd57560769c0
-- title:
--   P2 M Ground Theory Heights  Heights is Small H one whole Point 586e1e8d0445: P2 M Ground Theory Heights  Heights is Small H one whole Point 586e1e8d0445
-- statement:
--   The P2 M Ground Theory Heights  Heights is Small H one whole Point 586e1e8d0445 construction uses the P2 M Ground Theory Heights  Heights is Small H one whole Point 586e1e8d0445 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L466-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L466-L474

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

theorem P2M_GroundTheory_Heights__Heights_isSmallH_one_wholePoint_586e1e8d0445 [Fintype ι] (N : Geo.HermLine (blockIdx n)) :
    Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) (wholePoint n)) (wholePoint n) N 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isSmallH_one_wholePoint» := P2M_GroundTheory_Heights__Heights_isSmallH_one_wholePoint_586e1e8d0445
