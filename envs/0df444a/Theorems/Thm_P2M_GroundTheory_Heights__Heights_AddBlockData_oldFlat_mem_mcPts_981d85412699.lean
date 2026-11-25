-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_oldFlat_mem_mcPts_981d85412699
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_oldFlat_mem_mcPts_981d85412699
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:22.038402+00:00
-- url     : https://prove2.me/theorems/014db763-8b47-4299-872a-9c21bc9e9bc8
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data old Flat mem mc Pts 981d85412699: P2 M Ground Theory Heights  Heights Add Block Data old Flat mem mc Pts 981d85412699
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data old Flat mem mc Pts 981d85412699 construction uses the P2 M Ground Theory Heights  Heights Add Block Data old Flat mem mc Pts 981d85412699 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L137-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L137-L159

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

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_oldFlat_mem_mcPts_981d85412699 {P : ArithVariety n} (D : AddBlockData P) {Ω : Type} [Field Ω]
    (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) (z : Coord D.extSizes → ℂ)
    (hz : z ∈ Geo.mcPts (ι := blockIdx D.extSizes)
        (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x'))) :
    D.oldFlat z ∈ Geo.mcPts (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«oldFlat_mem_mcPts» := P2M_GroundTheory_Heights__Heights_AddBlockData_oldFlat_mem_mcPts_981d85412699
