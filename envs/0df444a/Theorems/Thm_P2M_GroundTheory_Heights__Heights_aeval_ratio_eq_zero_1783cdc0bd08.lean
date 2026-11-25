-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_ratio_eq_zero_1783cdc0bd08
-- name    : P2M_GroundTheory_Heights__Heights_aeval_ratio_eq_zero_1783cdc0bd08
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:16.736061+00:00
-- url     : https://prove2.me/theorems/dc6a34bc-3e0a-4ddb-9f63-898199de6c0d
-- title:
--   P2 M Ground Theory Heights  Heights aeval ratio eq zero 1783cdc0bd08: P2 M Ground Theory Heights  Heights aeval ratio eq zero 1783cdc0bd08
-- statement:
--   The P2 M Ground Theory Heights  Heights aeval ratio eq zero 1783cdc0bd08 construction uses the P2 M Ground Theory Heights  Heights aeval ratio eq zero 1783cdc0bd08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L66-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L66-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegreeRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
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
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_aeval_ratio_eq_zero_1783cdc0bd08 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ} (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x))
    (hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0) (f : MvPolynomial (Coord n) ℚ)
    (hf : aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0) :
    aeval (fun p ↦ z p / z ⟨p.1, c p.1⟩) f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aeval_ratio_eq_zero» := P2M_GroundTheory_Heights__Heights_aeval_ratio_eq_zero_1783cdc0bd08
