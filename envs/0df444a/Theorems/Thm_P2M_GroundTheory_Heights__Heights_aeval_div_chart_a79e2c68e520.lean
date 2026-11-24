-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_div_chart_a79e2c68e520
-- name    : P2M_GroundTheory_Heights__Heights_aeval_div_chart_a79e2c68e520
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:33.149993+00:00
-- url     : https://prove2.me/theorems/b0a06413-0379-4050-b802-b4db23b9cffb
-- title:
--   P2 M Ground Theory Heights  Heights aeval div chart a79e2c68e520: P2 M Ground Theory Heights  Heights aeval div chart a79e2c68e520
-- statement:
--   The P2 M Ground Theory Heights  Heights aeval div chart a79e2c68e520 construction uses the P2 M Ground Theory Heights  Heights aeval div chart a79e2c68e520 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L36-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L36-L54

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

theorem P2M_GroundTheory_Heights__Heights_aeval_div_chart_a79e2c68e520 {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (G : MvPolynomial (Coord n) ℤ) (d : ι → ℕ) (hG : IsWeightedHomogeneous (coordDeg n) G d) :
    aeval (fun p ↦ z p / z ⟨p.1, c p.1⟩) G = aeval z G * ∏ k, (z ⟨k, c k⟩ ^ d k)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aeval_div_chart» := P2M_GroundTheory_Heights__Heights_aeval_div_chart_a79e2c68e520
