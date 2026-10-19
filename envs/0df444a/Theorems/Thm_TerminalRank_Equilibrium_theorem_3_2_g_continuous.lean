-- Prove2me | Theorems.Thm_TerminalRank_Equilibrium_theorem_3_2_g_continuous
-- name    : TerminalRank.Equilibrium.theorem_3_2_g_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:09.116818+00:00
-- url     : https://prove2.me/theorems/659da5cd-31d2-4dda-9741-8d677c43185c
-- title:
--   Proof of Theorem 3.2, p. 8 — g is continuous on the compact interval containing its range
-- statement:
--   Let $c>0$, $\sigma>0$, $T>0$, $x_0\in\mathbb R$ and $R\in\mathcal R^{rm}_b$. The map
--   $$g(m)=x_0+\sigma\sqrt T\int_0^1N^{-1}\!\Big(\frac{\int_0^r e^{-R(z,m)/2c\sigma^2}dz}{\int_0^1 e^{-R(z,m)/2c\sigma^2}dz}\Big)dr$$
--   is continuous on the compact interval $\{m: |(m-x_0)/(\sigma\sqrt T)|\le C\sqrt{2/\pi}\}$ containing its range, where $C=\exp(\|R(1,\cdot)-R(0,\cdot)\|_\infty/(2c\sigma^2))$.
--
--   Together with the bound on its range, continuity yields a fixed point of $g$, that is, a solution of (3.3); this is how the paper obtains existence of an equilibrium.
-- source:
--   Bayraktar & Zhang, Terminal Ranking Games, arXiv:1906.09628v2, p. 8, proof of Theorem 3.2, last sentences

import Mathlib
import Definitions.Def_TerminalRank_Equilibrium_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TerminalRank.Equilibrium

/-- Proof of Theorem 3.2, p. 8 (Bayraktar–Zhang, arXiv:1906.09628v2), last sentences: for
`R ∈ ℛʳᵐ_b` the right-hand side `g` of (3.3) is continuous on the compact interval containing
its range (because `R` is continuous in `m`). -/
theorem theorem_3_2_g_continuous (x0 σ c : ℝ) (T : ℝ≥0)
    (hσ : 0 < σ) (hc : 0 < c) (hT : 0 < T)
    (R : ℝ → ℝ → ℝ) (hR : IsRMReward R) :
    ContinuousOn (gmap x0 σ c T R)
      {m : ℝ | |(m - x0) / (σ * Real.sqrt T)| ≤
        Real.exp ((⨆ m' : ℝ, (R 1 m' - R 0 m')) / (2 * c * σ ^ 2)) *
          Real.sqrt (2 / Real.pi)} := by sorry

end TerminalRank.Equilibrium
