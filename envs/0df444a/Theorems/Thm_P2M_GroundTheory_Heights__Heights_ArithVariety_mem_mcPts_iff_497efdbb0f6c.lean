-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:23.693865+00:00
-- url     : https://prove2.me/theorems/f1c98551-23fb-4590-8e5b-4489206686f5
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety mem mc Pts iff 497efdbb0f6c: P2 M Ground Theory Heights  Heights Arith Variety mem mc Pts iff 497efdbb0f6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety mem mc Pts iff 497efdbb0f6c construction uses the P2 M Ground Theory Heights  Heights Arith Variety mem mc Pts iff 497efdbb0f6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L39-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c (P : ArithVariety n) (w : Coord n → ℂ) :
    w ∈ Geo.mcPts P.ideal ↔ unflatCone w ∈ P.points ℂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«mem_mcPts_iff» := P2M_GroundTheory_Heights__Heights_ArithVariety_mem_mcPts_iff_497efdbb0f6c
