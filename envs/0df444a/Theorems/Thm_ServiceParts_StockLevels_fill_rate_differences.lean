-- Prove2me | Theorems.Thm_ServiceParts_StockLevels_fill_rate_differences
-- name    : ServiceParts.StockLevels.fill_rate_differences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:54:53.977779+00:00
-- url     : https://prove2.me/theorems/d0bc4a84-4842-43b7-b3db-31f5cb7fa6af
-- title:
--   Section 3.3, p. 53 — ΔF(s) = p(s|λτ̄), Δ²F(s) = p(s|λτ̄)(λτ̄/(s+1) − 1): the Poisson fill rate is concave exactly from ⌊λτ̄⌋ on
-- statement:
--   Let demand be a simple Poisson process and let $a = \lambda\bar\tau > 0$ be the mean number of units in resupply, so that $p(x \mid a) = e^{-a}a^x/x!$. The fill rate at stock level $s$ is $F(s) = \sum_{x < s} p(x \mid a)$. Then for every $s \ge 0$:
--
--   1. $\Delta F(s) = F(s+1) - F(s) = p(s \mid a) = e^{-a}\,a^s/s!$;
--   2. $$\Delta^2 F(s) = e^{-a}\frac{a^{s+1}}{(s+1)!} - e^{-a}\frac{a^{s}}{s!} = e^{-a}\frac{a^s}{s!}\Big(\frac{a}{s+1} - 1\Big);$$
--   3. if $a > s + 1$ then $\Delta^2 F(s) > 0$ (the fill rate is not concave there);
--   4. if $a$ is not an integer, $\Delta^2 F(s) \le 0$ if and only if $s \ge \lfloor a \rfloor$;
--   5. if $a$ is an integer, $\Delta^2 F(s) \le 0$ if and only if $s \ge a - 1$.
--
--   This is why stock levels in fill-rate optimization problems are restricted to $s \ge \lfloor\lambda\bar\tau\rfloor$: only there is the fill rate discretely concave.
--
--   **Formalization Note** $\lambda$ and $\bar\tau$ are positive reals and $a = \lambda\bar\tau$. "Integer" means $a = n$ for a natural number $n$, which is the only possibility since $a > 0$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 52-53, Section 3.3 (F(s), ΔF(s), Δ²F(s) and the concavity region)

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic

namespace ServiceParts.StockLevels

theorem fill_rate_differences (lam tbar : ℝ) (hlam : 0 < lam) (htbar : 0 < tbar) (s : ℕ) :
    fdiff (poissonFillRate (lam * tbar)) s = poissonPmf (lam * tbar) s ∧
    fdiff2 (poissonFillRate (lam * tbar)) s
      = poissonPmf (lam * tbar) (s + 1) - poissonPmf (lam * tbar) s ∧
    fdiff2 (poissonFillRate (lam * tbar)) s
      = poissonPmf (lam * tbar) s * (lam * tbar / ((s : ℝ) + 1) - 1) ∧
    ((s : ℝ) + 1 < lam * tbar → 0 < fdiff2 (poissonFillRate (lam * tbar)) s) ∧
    ((¬ ∃ n : ℕ, lam * tbar = n) →
      (fdiff2 (poissonFillRate (lam * tbar)) s ≤ 0 ↔ ⌊lam * tbar⌋₊ ≤ s)) ∧
    ((∃ n : ℕ, lam * tbar = n) →
      (fdiff2 (poissonFillRate (lam * tbar)) s ≤ 0 ↔ lam * tbar - 1 ≤ (s : ℝ))) := by sorry

end ServiceParts.StockLevels
