-- Prove2me | Theorems.Thm_Rudin_ch11_monotone_convergence
-- name    : Rudin.ch11_monotone_convergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:24:49.557412+00:00
-- url     : https://prove2.me/theorems/6d7d1f7f-349a-42fc-80be-5008347f46f6
-- title:
--   Theorem 11.28 — Lebesgue's monotone convergence theorem
-- statement:
--   If $0 \le f_1 \le f_2 \le \cdots$ are measurable and $f_n(x) \to f(x)$ for every $x$, then $\int f_n\,d\mu \to \int f\,d\mu$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 319, Theorem 11.28

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory
open scoped ENNReal

namespace Rudin

/-- Rudin, Theorem 11.28 (Lebesgue's monotone convergence theorem): if `0 ≤ f 0 ≤ f 1 ≤ ⋯` are
measurable and converge pointwise to `g`, then the integrals converge to the integral of
`g`. -/
theorem ch11_monotone_convergence {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hmono : ∀ x, Monotone fun n => f n x)
    (g : X → ℝ≥0∞) (hg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, g x ∂μ)) := by sorry

end Rudin
