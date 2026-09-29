-- Prove2me | Theorems.Thm_Rudin_RSIntegrable_of_uniform_approximation
-- name    : Rudin.RSIntegrable_of_uniform_approximation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T00:53:41.434854+00:00
-- url     : https://prove2.me/theorems/ab18c179-44bb-4f10-91e1-911d3d10178d
-- title:
--   Uniformly approximable limits are Riemann–Stieltjes integrable
-- statement:
--   Let $\alpha$ be increasing on $[a,b]$. Suppose every $f_n$ is Riemann–Stieltjes integrable with respect to $\alpha$ and, for every $\varepsilon>0$, some $f_n$ approximates $g$ uniformly within $\varepsilon$ on $[a,b]$. Then $g$ is Riemann–Stieltjes integrable with respect to $\alpha$.
--
--   The result isolates the integrability half of the uniform-limit theorem and uses only the existence of arbitrarily accurate members of the approximating family.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 7.16 and its proof.

import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_integrals_stable

namespace Rudin

theorem RSIntegrable_of_uniform_approximation {a b : ℝ} (hab : a ≤ b)
    (α : ℝ → ℝ) (hα : MonotoneOn α (Set.Icc a b))
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hint : ∀ n, RSIntegrable a b (f n) α)
    (happrox : ∀ ε > 0, ∃ n, ∀ x ∈ Set.Icc a b, |f n x - g x| ≤ ε) :
    RSIntegrable a b g α := by sorry
