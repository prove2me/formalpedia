-- Prove2me | Theorems.Thm_QueueingFundamentals_Networks_marginal_recursion
-- name    : QueueingFundamentals.Networks.marginal_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:11:42.57138+00:00
-- url     : https://prove2.me/theorems/0bae2383-9d6f-401a-9df5-736cdd9fe4d9
-- title:
--   Eq. (4.26) — the marginal-probability recursion of a closed Jackson network
-- statement:
--   Consider a closed Jackson network of $k \ge 1$ nodes, each with a single exponential server of rate $\mu_i > 0$, and an irreducible routing matrix $R = (r_{ij})$ with rows summing to one. For each population $N = 0, 1, 2, \dots$ let $p_N$ be the steady-state distribution of the $N$-customer network (the probability solution of the balance equations (4.14)), let
--   $$p_i(n, N) = \Pr\{N_i = n \mid N \text{ customers in network}\}$$
--   be the marginal probability of $n$ customers at node $i$, and let
--   $$\lambda_i(N) = \Pr\{\text{server busy at node } i\}\cdot\mu_i$$
--   be the throughput of node $i$. Then $p_i(0, 0) = 1$ and
--   $$p_i(n, N) = \frac{\lambda_i(N)}{\mu_i}\,p_i(n-1, N-1) \qquad (n, N \ge 1).$$
--
--   The recursion is the closed-network analogue of $p_n = \rho p_{n-1}$ for the $M/M/1$ queue: combined with mean-value analysis, it yields every nodal marginal distribution population by population, without computing the normalizing constant.
--
--   **Formalization Note** $\lambda_i(N)$ is not a free parameter: it is the throughput computed from $p_N$, as in the book's proof (p.209). No traffic-equation solution appears in the statement; its existence follows from the irreducibility of $R$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.204, Eq. (4.26); proof pp.207–209

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

/-- Eq. (4.26), p.204 (proved pp.207–209): for a closed Jackson network of `k ≥ 1` single-server
nodes (rates `μ_i > 0`, irreducible routing `R`) and its steady-state distributions `p_N`
(`N = 0, 1, 2, …`), the marginal probabilities `p_i(n, N)` satisfy `p_i(0, 0) = 1` and
`p_i(n, N) = (λ_i(N)/μ_i) p_i(n − 1, N − 1)` for `n, N ≥ 1`, where
`λ_i(N) = Pr{server busy at node i} · μ_i` is the throughput of node `i`. -/
theorem marginal_recursion {k : ℕ} [NeZero k] (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ)
    (hmu : ∀ i, 0 < mu i) (hR : IsRoutingMatrix R) (hirr : IsIrreducible R)
    (p : ℕ → (Fin k → ℕ) → ℝ) (hp : ∀ N, IsClosedSteadyState mu R N (p N)) (i : Fin k) :
    marginal 0 (p 0) i 0 = 1 ∧
      ∀ n N : ℕ, 1 ≤ n → 1 ≤ N →
        marginal N (p N) i n =
          throughput mu N (p N) i / mu i * marginal (N - 1) (p (N - 1)) i (n - 1) := by sorry

end QueueingFundamentals.Networks
