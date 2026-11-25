-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_intersectionHeight_4dccfce91942
-- name    : P2M_GroundTheory_Heights__Heights_height_eq_intersectionHeight_4dccfce91942
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:03.166269+00:00
-- url     : https://prove2.me/theorems/bab41d8d-5d78-5ee7-a710-c747d1201196
-- title:
--   P2 M Ground Theory Heights  Heights height eq intersection Height 4dccfce91942: P2 M Ground Theory Heights  Heights height eq intersection Height 4dccfce91942
-- statement:
--   The P2 M Ground Theory Heights  Heights height eq intersection Height 4dccfce91942 construction uses the P2 M Ground Theory Heights  Heights height eq intersection Height 4dccfce91942 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L331-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L331-L336

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

theorem P2M_GroundTheory_Heights__Heights_height_eq_intersectionHeight_4dccfce91942 [Nonempty ι] (h₁ : OrbitCurve.Statement) (h₂ : OrbitDegree.Statement)
    (h₃ : HeightRecR.Statement)
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (hII : Geo.IsIntersectionFamily II) (A : HermLine n) {x : Cone n (AlgebraicClosure ℚ)}
    (hx : BlockNonzero x) : height A x = IndefiniteRowSideFullHecke.HeightsSet.height II A.toGeo (orbitIdeal x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_eq_intersectionHeight» := P2M_GroundTheory_Heights__Heights_height_eq_intersectionHeight_4dccfce91942
