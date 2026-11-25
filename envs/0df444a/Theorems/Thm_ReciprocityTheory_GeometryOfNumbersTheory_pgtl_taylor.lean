-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgtl_taylor
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.pgtl_taylor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:08.608533+00:00
-- url     : https://prove2.me/theorems/b28dffe7-6caf-4c4e-be48-91f84e211704
-- title:
--   Geometry Of Numbers Theory: pgtl taylor
-- statement:
--   The Geometry Of Numbers Theory construction uses the pgtl taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L99-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L99-L175

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.pgtl_taylor {D : ℕ} {ρ₀ K₃ : ℝ} (φ : (Fin D → ℂ) → ℝ)
    (hφ : ContDiffOn ℝ 3 φ (Metric.ball 0 ρ₀))
    (hK₃ : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ K₃)
    (z : Fin D → ℂ) (hz : z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀) :
    |φ z - φ 0 - fderiv ℝ φ 0 z - fderiv ℝ (fderiv ℝ φ) 0 z z / 2| ≤ K₃ * ‖z‖ ^ 3 := by sorry
