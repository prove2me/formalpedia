-- Prove2me | Theorems.Thm_ServiceParts_StockLevels_greedy_fill_rate_optimal
-- name    : ServiceParts.StockLevels.greedy_fill_rate_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:29:10.428044+00:00
-- url     : https://prove2.me/theorems/9acb6127-248e-4635-9ad0-c39a25a113bb
-- title:
--   Section 3.4.3, p. 65 — every greedy marginal-analysis solution is optimal for Problem 5 at its own budget
-- statement:
--   Consider $n \ge 1$ item types, item $i$ with simple Poisson demand of rate $\lambda_i > 0$, mean repair time $\bar\tau_i > 0$, unit cost $c_i > 0$ and fill rate $F_i(s) = \sum_{x < s} e^{-\lambda_i\bar\tau_i}(\lambda_i\bar\tau_i)^x/x!$. Problem 5 (3.41) is
--   $$\max \sum_{i=1}^n \frac{\lambda_i}{\sum_j \lambda_j}\,F_i(s_i) \quad\text{s.t.}\quad \sum_{i=1}^n c_i s_i \le b,\quad s_i \ge \lfloor \lambda_i\bar\tau_i \rfloor \text{ and integral}.$$
--   Run the greedy procedure: start from $s_i = \lfloor\lambda_i\bar\tau_i\rfloor$ and repeatedly raise by one the stock level of an item $i^*$ maximizing
--   $$\Delta_i(s_i) = \frac{\lambda_i}{\sum_j \lambda_j}\cdot\frac{F_i(s_i + 1) - F_i(s_i)}{c_i},$$
--   with ties broken arbitrarily. Let $s^{(k)}$ be the stock vector after $k$ steps. Then for every $k \ge 0$, $s^{(k)}$ is an optimal solution of Problem 5 with budget
--   $$b = \sum_{i=1}^n c_i\,s^{(k)}_i:$$
--   it satisfies the floor constraints, and every integer vector $s$ with $s_i \ge \lfloor\lambda_i\bar\tau_i\rfloor$ and $\sum_i c_i s_i \le b$ has average fill rate at most that of $s^{(k)}$.
--
--   The case $k = 1$ is the book's displayed solution; the book states that continuing in this manner the greedy algorithm finds the optimal solution for the budgets it generates.
--
--   **Formalization Note** The greedy procedure is a relation on sequences, so the statement covers every tie-breaking rule.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 64-65, Section 3.4.3, Problem 5, Eq. (3.41), and the greedy procedure

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem greedy_fill_rate_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lam tbar c : ι → ℝ) (hlam : ∀ i, 0 < lam i) (htbar : ∀ i, 0 < tbar i)
    (hc : ∀ i, 0 < c i) (seq : ℕ → ι → ℕ) (hseq : IsGreedySeq lam tbar c seq) (k : ℕ) :
    (∀ i, ⌊lam i * tbar i⌋₊ ≤ seq k i) ∧
    ∀ s : ι → ℕ, (∀ i, ⌊lam i * tbar i⌋₊ ≤ s i) →
      ∑ i, c i * (s i : ℝ) ≤ ∑ i, c i * (seq k i : ℝ) →
      avgFillRate lam tbar s ≤ avgFillRate lam tbar (seq k) := by sorry

end ServiceParts.StockLevels
