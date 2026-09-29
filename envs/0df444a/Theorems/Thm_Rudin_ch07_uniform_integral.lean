-- Prove2me | Theorems.Thm_Rudin_ch07_uniform_integral
-- name    : Rudin.ch07_uniform_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:22:09.361068+00:00
-- url     : https://prove2.me/theorems/cbb611c9-38f7-4e89-b494-fdad54ee7dc6
-- title:
--   Theorem 7.16 — uniform convergence and integration
-- statement:
--   Let $\alpha$ be monotonically increasing on $[a,b]$, let $f_n \in \mathcal{R}(\alpha)$, and suppose $f_n \to g$ uniformly on $[a,b]$. Then $g \in \mathcal{R}(\alpha)$ and $\int_a^b f_n\,d\alpha \to \int_a^b g\,d\alpha$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, p. 151, Theorem 7.16

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 7.16: if `f n ∈ ℛ(α)` on `[a, b]` and `f n → g` uniformly on `[a, b]`,
then `g ∈ ℛ(α)` and `∫ f n dα → ∫ g dα`. -/
theorem ch07_uniform_integral (a b : ℝ) (hab : a ≤ b) (α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hint : ∀ n, RSIntegrable a b (f n) α)
    (huc : TendstoUniformlyOn f g atTop (Set.Icc a b)) :
    RSIntegrable a b g α ∧
      Tendsto (fun n => RSIntegral a b (f n) α) atTop (𝓝 (RSIntegral a b g α)) := by sorry

end Rudin
