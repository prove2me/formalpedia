-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_isWeightedHomogeneous_eq_of_chart_999ddb890695
-- name    : P2M_GroundTheory_Heights__Heights_exists_isWeightedHomogeneous_eq_of_chart_999ddb890695
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:27.530157+00:00
-- url     : https://prove2.me/theorems/72462afc-be6c-43dc-81d0-061119ee8cc1
-- title:
--   P2 M Ground Theory Heights  Heights exists is Weighted Homogeneous eq of chart 999ddb890695: P2 M Ground Theory Heights  Heights exists is Weighted Homogeneous eq of chart 999ddb890695
-- statement:
--   The P2 M Ground Theory Heights  Heights exists is Weighted Homogeneous eq of chart 999ddb890695 construction uses the P2 M Ground Theory Heights  Heights exists is Weighted Homogeneous eq of chart 999ddb890695 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L14-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_exists_isWeightedHomogeneous_eq_of_chart_999ddb890695 {R : Type*} [CommRing R]
    (χ : MvPolynomial (Coord n) ℤ →+* R) (c : (k : ι) → Fin (n k + 1))
    (hχ : ∀ k, χ (X ⟨k, c k⟩) = 1) (g : MvPolynomial (Coord n) ℤ) :
    ∃ (D : ι → ℕ) (G : MvPolynomial (Coord n) ℤ),
      IsWeightedHomogeneous (coordDeg n) G D ∧ χ G = χ g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_isWeightedHomogeneous_eq_of_chart» := P2M_GroundTheory_Heights__Heights_exists_isWeightedHomogeneous_eq_of_chart_999ddb890695
