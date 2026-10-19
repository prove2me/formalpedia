-- Prove2me | Theorems.Thm_TerminalRank_Equilibrium_theorem_3_2_bound_g
-- name    : TerminalRank.Equilibrium.theorem_3_2_bound_g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:02.731546+00:00
-- url     : https://prove2.me/theorems/ef7123f8-0957-423c-a0dc-8135fc054e87
-- title:
--   Proof of Theorem 3.2, p. 8, display — |(g(m) − x0)/(σ√T)| ≤ C∫₀¹|N⁻¹(y)|dy = C√(2/π)
-- statement:
--   Let $c>0$, $\sigma>0$, $T>0$, $x_0\in\mathbb R$, and let $R\in\mathcal R^{rm}_b$. Let $g(m)$ be the right-hand side of (3.3),
--   $$g(m)=x_0+\sigma\sqrt T\int_0^1N^{-1}\!\Big(\frac{\int_0^r e^{-R(z,m)/2c\sigma^2}dz}{\int_0^1 e^{-R(z,m)/2c\sigma^2}dz}\Big)dr,$$
--   and set $C=\exp\big(\|R(1,\cdot)-R(0,\cdot)\|_\infty/2c\sigma^2\big)$, where $\|R(1,\cdot)-R(0,\cdot)\|_\infty=\sup_m\,(R(1,m)-R(0,m))$. Then for every $m\in\mathbb R$
--   $$\Big|\frac{g(m)-x_0}{\sigma\sqrt T}\Big|\le C\int_0^1|N^{-1}(y)|\,dy,\qquad\text{and}\qquad\int_0^1|N^{-1}(y)|\,dy=\sqrt{2/\pi}.$$
--
--   The bound confines the range of $g$ to a compact interval, which is the first half of the existence argument for (3.3).
--
--   **Formalization Note.** Since $R$ is weakly increasing in $r$, $R(1,m)-R(0,m)\ge0$, so the sup norm is the supremum written above; the supremum is over a nonempty set bounded by $2\sup|R|$.
-- source:
--   Bayraktar & Zhang, Terminal Ranking Games, arXiv:1906.09628v2, p. 8, proof of Theorem 3.2, display

import Mathlib
import Definitions.Def_TerminalRank_Equilibrium_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TerminalRank.Equilibrium

/-- Proof of Theorem 3.2, p. 8 (Bayraktar–Zhang, arXiv:1906.09628v2), display: for `R ∈ ℛʳᵐ_b`
and `C = exp(‖R(1, ·) − R(0, ·)‖_∞ / (2cσ²))`, the map `g` of (3.3) satisfies
`|(g(m) − x0)/(σ√T)| ≤ C ∫_0^1 |N⁻¹(y)| dy`, and `∫_0^1 |N⁻¹(y)| dy = √(2/π)`. -/
theorem theorem_3_2_bound_g (x0 σ c : ℝ) (T : ℝ≥0)
    (hσ : 0 < σ) (hc : 0 < c) (hT : 0 < T)
    (R : ℝ → ℝ → ℝ) (hR : IsRMReward R) :
    (∀ m : ℝ, |(gmap x0 σ c T R m - x0) / (σ * Real.sqrt T)| ≤
      Real.exp ((⨆ m' : ℝ, (R 1 m' - R 0 m')) / (2 * c * σ ^ 2)) *
        ∫ y in (0 : ℝ)..1, |Ninv y|) ∧
    ∫ y in (0 : ℝ)..1, |Ninv y| = Real.sqrt (2 / Real.pi) := by sorry

end TerminalRank.Equilibrium
