-- Prove2me | Theorems.Thm_Rudin_ch03_radius_of_convergence
-- name    : Rudin.ch03_radius_of_convergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:16:01.061734+00:00
-- url     : https://prove2.me/theorems/f9345205-c07f-4a11-b6fe-7b7c2e34a740
-- title:
--   Theorem 3.39 — radius of convergence of a power series
-- statement:
--   For the power series $\sum c_n z^n$ put $\alpha = \limsup_n \|c_n\|^{1/n}$ and $R = 1/\alpha$ (with $R = \infty$ when $\alpha = 0$ and $R = 0$ when $\alpha = \infty$). The series converges when $\|z\| < R$ and diverges when $\|z\| > R$. The formal statement writes the two conditions as $\alpha\|z\| < 1$ and $\alpha\|z\| > 1$ to avoid inverting in the extended reals.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 69, Definition 3.38 and Theorem 3.39

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.39: given the power series `∑ cₙ zⁿ`, put `α = limsup ‖cₙ‖^{1/n}` and
`R = 1/α` (so `R = ∞` when `α = 0` and `R = 0` when `α = ∞`).  Then the series converges when
`‖z‖ < R` and diverges when `‖z‖ > R`.  The two cases are stated here as `α ‖z‖ < 1` and
`α ‖z‖ > 1`, which avoids dividing in the extended reals. -/
theorem ch03_radius_of_convergence (c : ℕ → ℂ) (z : ℂ) (α : EReal)
    (hα : α = limsup (fun n => ((‖c n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop) :
    (α * (‖z‖ : EReal) < 1 → SeriesConverges fun n => c n * z ^ n) ∧
    (1 < α * (‖z‖ : EReal) → ¬ SeriesConverges fun n => c n * z ^ n) := by sorry

end Rudin
