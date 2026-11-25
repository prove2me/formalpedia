-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_8221f24f898f
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_8221f24f898f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:32:15.036344+00:00
-- url     : https://prove2.me/theorems/dea7a44b-464d-4b89-b17c-4eaed1e47af4
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max aeval dehom Coords 8221f24f898f: P2 M Ground Theory Heights  Heights Orbit Chart Max aeval dehom Coords 8221f24f898f
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max aeval dehom Coords 8221f24f898f construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max aeval dehom Coords 8221f24f898f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L68-L75

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_8221f24f898f {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (F : MvPolynomial (Coord n) ℤ) :
    aeval (dehomCoords z c) F =
      aeval z (homogenize c F) * ∏ k, (z ⟨k, c k⟩)⁻¹ ^ homDeg F k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«aeval_dehomCoords» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_dehomCoords_8221f24f898f
