-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_intersectionHeight_eq_height_9b57ee73823f
-- name    : P2M_GroundTheory_Heights__Heights_intersectionHeight_eq_height_9b57ee73823f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:22.543109+00:00
-- url     : https://prove2.me/theorems/e672735e-2a62-54fc-92bd-a053d07f854c
-- title:
--   P2 M Ground Theory Heights  Heights intersection Height eq height 9b57ee73823f: P2 M Ground Theory Heights  Heights intersection Height eq height 9b57ee73823f
-- statement:
--   The P2 M Ground Theory Heights  Heights intersection Height eq height 9b57ee73823f construction uses the P2 M Ground Theory Heights  Heights intersection Height eq height 9b57ee73823f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L338-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L338-L347

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_intersectionHeight_eq_height_9b57ee73823f [Nonempty ι] (h₁ : OrbitCurve.Statement) (h₂ : OrbitDegree.Statement)
    (h₃ : HeightRecR.Statement)
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (hII : Geo.IsIntersectionFamily II) (B : Geo.HermLine (blockIdx n)) (hB : Geo.IsSmoothHerm B)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    IndefiniteRowSideFullHecke.HeightsSet.height II B (orbitIdeal x) = height (HermLine.ofGeo B hB) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«intersectionHeight_eq_height» := P2M_GroundTheory_Heights__Heights_intersectionHeight_eq_height_9b57ee73823f
