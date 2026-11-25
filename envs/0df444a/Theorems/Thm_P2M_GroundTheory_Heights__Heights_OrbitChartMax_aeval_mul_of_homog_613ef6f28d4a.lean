-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_mul_of_homog_613ef6f28d4a
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_mul_of_homog_613ef6f28d4a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:21.954913+00:00
-- url     : https://prove2.me/theorems/d5a29028-72f7-4a88-93b7-8ff572ea627a
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max aeval mul of homog 613ef6f28d4a: P2 M Ground Theory Heights  Heights Orbit Chart Max aeval mul of homog 613ef6f28d4a
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max aeval mul of homog 613ef6f28d4a construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max aeval mul of homog 613ef6f28d4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L22-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L22-L41

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_mul_of_homog_613ef6f28d4a {R : Type*} [CommRing R] [Algebra ℤ R] (t : ι → R) (z : Coord n → R)
    {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hG : IsWeightedHomogeneous (coordDeg n) G b) :
    aeval (fun p ↦ t p.1 * z p) G = aeval z G * ∏ k, t k ^ b k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«aeval_mul_of_homog» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_mul_of_homog_613ef6f28d4a
