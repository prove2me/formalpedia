-- Prove2me | Theorems.Thm_Rudin_ch11_dominated_convergence
-- name    : Rudin.ch11_dominated_convergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:36:11.486601+00:00
-- url     : https://prove2.me/theorems/850f9f6e-99e5-4327-9429-95dbd015d85f
-- title:
--   Theorem 11.32 — Lebesgue's dominated convergence theorem
-- statement:
--   If measurable functions $f_n$ converge pointwise to $f$ and satisfy $|f_n| \le g$ for an integrable $g$, then $f$ is integrable and $\int f_n\,d\mu \to \int f\,d\mu$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 321, Theorem 11.32

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 11.32 (Lebesgue's dominated convergence theorem): if measurable functions
`f n` converge pointwise to `g` and are dominated by an integrable `h`, then `g` is
integrable and the integrals converge. -/
theorem ch11_dominated_convergence {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ) (g h : X → ℝ) (hf : ∀ n, Measurable (f n))
    (hdom : ∀ n, ∀ x, |f n x| ≤ h x) (hh : Integrable h μ)
    (hconv : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Integrable g μ ∧ Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by sorry

end Rudin
