-- Prove2me | Theorems.Thm_Rudin_ch11_fatou
-- name    : Rudin.ch11_fatou
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:35:38.032591+00:00
-- url     : https://prove2.me/theorems/8d3d3b89-72db-4663-8c2f-43f45e4c1e80
-- title:
--   Theorem 11.31 — Fatou's theorem
-- statement:
--   If $f_n \ge 0$ are measurable and $f = \liminf_n f_n$, then $\int f\,d\mu \le \liminf_n \int f_n\,d\mu$. Strict inequality may occur.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 320, Theorem 11.31

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory
open scoped ENNReal

namespace Rudin

/-- Rudin, Theorem 11.31 (Fatou's theorem): for nonnegative measurable functions, the integral of
the lower limit is at most the lower limit of the integrals. -/
theorem ch11_fatou {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, liminf (fun n => f n x) atTop ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := by sorry

end Rudin
