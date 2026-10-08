-- Prove2me | Theorems.Thm_QueueingFundamentals_Networks_tail_marginal
-- name    : QueueingFundamentals.Networks.tail_marginal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:11:41.465255+00:00
-- url     : https://prove2.me/theorems/1567c326-e883-47df-b27b-545c0826cd16
-- title:
--   The complementary marginal of a closed network: Pr{N_i ≥ n_i} = ρ_i^{n_i} G(N − n_i)/G(N)
-- statement:
--   Consider a closed network of $k$ single-server nodes with $\rho_1, \dots, \rho_k > 0$ and the product-form distribution (4.15) with $N$ customers,
--   $$p_{n_1,\dots,n_k} = \frac{1}{G(N)}\rho_1^{n_1}\cdots\rho_k^{n_k}, \qquad G(N) = \sum_{n_1+\cdots+n_k=N}\rho_1^{n_1}\cdots\rho_k^{n_k}.$$
--   For every node $i$ and every $0 \le n_i \le N$, the complementary marginal distribution is
--   $$\bar P_i(n_i; N) \equiv \Pr\{N_i \ge n_i \mid N \text{ customers in network}\} = \frac{\rho_i^{\,n_i}}{G(N)}\,G(N - n_i).$$
--
--   This identity is the core of the proof of the marginal recursion (4.26): taking $n_i = 1$ gives the server-busy probability, hence the throughput $\lambda_i(N) = \mu_i\rho_i G(N-1)/G(N)$.
--
--   **Formalization Note** $G(N - n_i)$ is the normalizing constant of the same network with $N - n_i$ customers; the hypothesis $n_i \le N$ matches the page (for $n_i > N$ the probability is $0$).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.208, the unnumbered display of P̄_i(n_i; N) in the proof of Eq. (4.26)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

/-- The complementary marginal, p.208 (proof of (4.26)): in a closed network of single-server nodes
with `ρ_i > 0`, under the product form (4.15) with `N` customers,
`P̄_i(m; N) = Pr{N_i ≥ m} = ρ_i^{m} G(N − m) / G(N)` for `0 ≤ m ≤ N`, where `G` is the normalizing
constant of (4.15). -/
theorem tail_marginal {k : ℕ} (rho : Fin k → ℝ) (hrho : ∀ i, 0 < rho i) (N m : ℕ) (hm : m ≤ N)
    (i : Fin k) :
    tailMarginal N (productForm (fun j n => rho j ^ n) N) i m =
      rho i ^ m * normConst (fun j n => rho j ^ n) (N - m) /
        normConst (fun j n => rho j ^ n) N := by sorry

end QueueingFundamentals.Networks
