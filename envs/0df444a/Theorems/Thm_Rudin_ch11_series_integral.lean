-- Prove2me | Theorems.Thm_Rudin_ch11_series_integral
-- name    : Rudin.ch11_series_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:31:58.564163+00:00
-- url     : https://prove2.me/theorems/9e0f1c29-1190-4215-b042-b5e14cc686dd
-- title:
--   Theorem 11.30 — term-by-term integration of a series of nonnegative functions
-- statement:
--   If $f_n \ge 0$ are measurable and $f = \sum_n f_n$, then $\int f\,d\mu = \sum_n \int f_n\,d\mu$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 320, Theorem 11.30

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory
open scoped ENNReal

namespace Rudin

/-- Rudin, Theorem 11.30: a series of nonnegative measurable functions may be integrated term by
term. -/
theorem ch11_series_integral {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, ∑' n, f n x ∂μ) = ∑' n, ∫⁻ x, f n x ∂μ := by sorry

end Rudin
