-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_of_homog_af572b81c448
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_of_homog_af572b81c448
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:03.830583+00:00
-- url     : https://prove2.me/theorems/ee99e2e8-8c00-4b89-8012-2d8384591de5
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max aeval dehom Coords of homog af572b81c448: P2 M Ground Theory Heights  Heights Orbit Chart Max aeval dehom Coords of homog af572b81c448
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max aeval dehom Coords of homog af572b81c448 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max aeval dehom Coords of homog af572b81c448 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L102-L106

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_of_homog_af572b81c448 {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω)
    (c : (k : ι) → Fin (n k + 1)) {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ}
    (hG : IsWeightedHomogeneous (coordDeg n) G b) :
    aeval (dehomCoords z c) G = aeval z G * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ b k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«aeval_dehomCoords_of_homog» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_of_homog_af572b81c448
