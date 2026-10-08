-- Prove2me | Theorems.Thm_QueueingFundamentals_Networks_last_node_marginal
-- name    : QueueingFundamentals.Networks.last_node_marginal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:11:16.586686+00:00
-- url     : https://prove2.me/theorems/31b548ca-642b-40f3-8fa6-db7a955f327e
-- title:
--   Eq. (4.22) — the marginal distribution at the last node via Buzen's functions
-- statement:
--   Consider a closed network of $k$ nodes with $c_i \ge 1$ servers at node $i$ and $\rho_i > 0$, whose $N$-customer joint distribution is the product form (4.17),
--   $$p_{n_1,\dots,n_k} = \frac{1}{G(N)}\prod_{i=1}^{k} f_i(n_i), \qquad f_i(n) = \frac{\rho_i^{\,n}}{a_i(n)},$$
--   with $G(N)$ and $g_m$ as in (4.19)–(4.20). Then the marginal distribution $p_k(n) = \Pr\{N_k = n\}$ of the number of customers at the last node $k$ is
--   $$p_k(n) = \frac{f_k(n)\, g_{k-1}(N - n)}{G(N)} \qquad (n = 0, 1, \dots, N).$$
--
--   Together with Buzen's recursion this yields a node's marginal distribution without summing over the joint distribution; any node can be made the last one by relabelling.
--
--   **Formalization Note** The network has $k+1$ nodes in Lean (`Fin (k + 1)`), the last one being `Fin.last k`, so the book's $g_{k-1}$ is `gBuzen … k`.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.199, Eq. (4.22)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

/-- Eq. (4.22), p.199: in a closed network of `k + 1` nodes (the last node is node `k + 1` of the book,
index `Fin.last k`) with `c_i ≥ 1` servers at node `i` and `ρ_i > 0`, under the product form (4.17)
the marginal distribution of the last node is `p_{k+1}(n) = f_{k+1}(n) g_k(N − n) / G(N)` for
`n = 0, 1, …, N`. -/
theorem last_node_marginal {k : ℕ} (rho : Fin (k + 1) → ℝ) (c : Fin (k + 1) → ℕ)
    (hrho : ∀ i, 0 < rho i) (hc : ∀ i, 1 ≤ c i) (N n : ℕ) (hn : n ≤ N) :
    marginal N (productForm (buzenFactor rho c) N) (Fin.last k) n =
      buzenFactor rho c (Fin.last k) n * gBuzen (buzenFactor rho c) k (Nat.le_succ k) (N - n) /
        normConst (buzenFactor rho c) N := by sorry

end QueueingFundamentals.Networks
