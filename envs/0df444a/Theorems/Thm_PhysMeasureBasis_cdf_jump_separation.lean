-- Prove2me | Theorems.Thm_PhysMeasureBasis_cdf_jump_separation
-- name    : PhysMeasureBasis.cdf_jump_separation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:53:01.127128+00:00
-- url     : https://prove2.me/theorems/18b8b389-c5ec-4317-a34e-11f24a1e2857
-- title:
--   `PhysMeasureBasis.cdf_jump_separation` (F G : ℝ → ℝ) (_hF : Monotone F) (_hG : Monotone G) (x₀ : ℝ) (hFc : ContinuousAt F x₀) (ε : ℝ) (hε : 0 < ε) (hjump : ∀ a b : ℝ, a <...
-- statement:
--   Prove the following Lean 4 theorem from `PhysMeasureBasis`.
--
--   `PhysMeasureBasis.cdf_jump_separation` (F G : ℝ → ℝ) (_hF : Monotone F) (_hG : Monotone G) (x₀ : ℝ) (hFc : ContinuousAt F x₀) (ε : ℝ) (hε : 0 < ε) (hjump : ∀ a b : ℝ, a < x₀ → x₀ < b → G b - G a ≥ ε) : ∃ a b : ℚ, (a:ℝ) < b ∧ |(G b - G a) - (F b - F a)| ≥ ε / 2
--
--   Formalization note: Lean 4 identifier `PhysMeasureBasis.cdf_jump_separation`.

-- Generated from PhysMeasureBasis.lean — theorem PhysMeasureBasis.cdf_jump_separation
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis


open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem PhysMeasureBasis.cdf_jump_separation (F G : ℝ → ℝ) (_hF : Monotone F) (_hG : Monotone G)
    (x₀ : ℝ) (hFc : ContinuousAt F x₀) (ε : ℝ) (hε : 0 < ε)
    (hjump : ∀ a b : ℝ, a < x₀ → x₀ < b → G b - G a ≥ ε) :
    ∃ a b : ℚ, (a:ℝ) < b ∧ |(G b - G a) - (F b - F a)| ≥ ε / 2 := by sorry
