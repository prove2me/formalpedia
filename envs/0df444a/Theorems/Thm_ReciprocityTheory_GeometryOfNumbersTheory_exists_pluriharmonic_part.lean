-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_exists_pluriharmonic_part
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.exists_pluriharmonic_part
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:54:24.384046+00:00
-- url     : https://prove2.me/theorems/9e8293c1-1437-4014-b3e8-2b206243d119
-- title:
--   Geometry Of Numbers Theory: exists pluriharmonic part
-- statement:
--   The Geometry Of Numbers Theory construction uses the exists pluriharmonic part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L177-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L177-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Complex

theorem ReciprocityTheory.GeometryOfNumbersTheory.exists_pluriharmonic_part {D : ℕ} {ρ₀ K₃ : ℝ} (φ : (Fin D → ℂ) → ℝ)
    (hφ : ContDiffOn ℝ 3 φ (Metric.ball 0 ρ₀))
    (hK₃ : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ K₃) :
    ∃ q : (Fin D → ℂ) → ℂ, Differentiable ℂ q ∧ q 0 = 0 ∧
      ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀,
        |φ z - φ 0 - (q z).re -
          (fderiv ℝ (fderiv ℝ φ) 0 z z + fderiv ℝ (fderiv ℝ φ) 0 (I • z) (I • z)) / 4| ≤
        K₃ * ‖z‖ ^ 3 := by sorry
