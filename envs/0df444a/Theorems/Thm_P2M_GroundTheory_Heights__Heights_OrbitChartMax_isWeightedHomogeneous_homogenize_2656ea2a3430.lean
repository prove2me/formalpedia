-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_isWeightedHomogeneous_homogenize_2656ea2a3430
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_isWeightedHomogeneous_homogenize_2656ea2a3430
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:41.088773+00:00
-- url     : https://prove2.me/theorems/cc7db3a1-598b-40b8-b70b-e080459c5391
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max is Weighted Homogeneous homogenize 2656ea2a3430: P2 M Ground Theory Heights  Heights Orbit Chart Max is Weighted Homogeneous homogenize 2656ea2a3430
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max is Weighted Homogeneous homogenize 2656ea2a3430 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max is Weighted Homogeneous homogenize 2656ea2a3430 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L51-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
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
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_isWeightedHomogeneous_homogenize_2656ea2a3430 (c : (k : ι) → Fin (n k + 1))
    (F : MvPolynomial (Coord n) ℤ) :
    IsWeightedHomogeneous (coordDeg n) (homogenize c F) (homDeg F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«isWeightedHomogeneous_homogenize» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_isWeightedHomogeneous_homogenize_2656ea2a3430
