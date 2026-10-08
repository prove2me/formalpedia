-- Prove2me | Theorems.Thm_QueueingFundamentals_Networks_mean_value_analysis
-- name    : QueueingFundamentals.Networks.mean_value_analysis
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:11:32.173206+00:00
-- url     : https://prove2.me/theorems/c581fe92-8cfa-4f86-826e-bdc60b958d2c
-- title:
--   Eqs. (4.23)–(4.25) — mean-value analysis of a closed Jackson network
-- statement:
--   Consider a closed Jackson network of $k \ge 1$ single-server nodes with service rates $\mu_i > 0$ and an irreducible routing matrix $R = (r_{ij})$, and for each population $N = 0, 1, 2, \dots$ let $p_N$ be its steady-state distribution (the probability solution of (4.14)). Write $L_i(N)$ for the mean number of customers at node $i$, $\lambda_i(N) = \Pr\{\text{server } i \text{ busy}\}\,\mu_i$ for the throughput of node $i$, and
--   $$W_i(N) = \frac{1 + L_i(N-1)}{\mu_i} \qquad (N \ge 1) \tag{4.23}$$
--   for the mean waiting time at node $i$. Then
--   1. $L_i(0) = 0$;
--   2. for $N \ge 1$ and every node $i$, Little's formula holds at each node:
--   $$L_i(N) = \lambda_i(N)\,W_i(N); \tag{4.24}$$
--   3. if $v$ solves the visit-ratio equations $v_i = \sum_{j=1}^{k} v_j r_{ji}$ (4.25) with $v_l = 1$ for a node $l$, then for $N \ge 1$
--   $$\lambda_l(N) = \frac{N}{\sum_{i=1}^{k} v_i W_i(N)}, \qquad \lambda_i(N) = \lambda_l(N)\,v_i \quad (i = 1, \dots, k).$$
--
--   Together these are the correctness of the MVA algorithm (steps (i)–(iii), p.202): starting from $L_i(0) = 0$, the quantities $W_i(n)$, $\lambda_i(n)$, $L_i(n)$ are computed for $n = 1, \dots, N$ without the normalizing constant.
--
--   **Formalization Note** The book argues (4.23) from the arrival theorem and (4.24) from Little's formula (p.201); here $L_i$ and $\lambda_i$ are defined from the steady-state distribution, and $W_i(N)$ is written out as $(1+L_i(N-1))/\mu_i$, so clause 2 is the content of (4.23) and (4.24) together.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.201–202, Eqs. (4.23), (4.24), (4.25) and the MVA algorithm, steps (i)–(iii)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

open Finset

/-- Eqs. (4.23)–(4.25) and the MVA algorithm, pp.201–202: for a closed Jackson network of `k ≥ 1`
single-server nodes (rates `μ_i > 0`, irreducible routing `R`) and its steady-state distributions
`p_N` (`N = 0, 1, 2, …`), with `L_i(N)` the mean number at node `i`, `λ_i(N)` the throughput and
`W_i(N) = (1 + L_i(N − 1))/μ_i` (4.23):
(1) `L_i(0) = 0`;
(2) `L_i(N) = λ_i(N) W_i(N)` for `N ≥ 1` (4.24);
(3) for any solution `v` of (4.25) with `v_l = 1`, and `N ≥ 1`:
`λ_l(N) = N / ∑_i v_i W_i(N)` and `λ_i(N) = λ_l(N) v_i`. -/
theorem mean_value_analysis {k : ℕ} [NeZero k] (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ)
    (hmu : ∀ i, 0 < mu i) (hR : IsRoutingMatrix R) (hirr : IsIrreducible R)
    (p : ℕ → (Fin k → ℕ) → ℝ) (hp : ∀ N, IsClosedSteadyState mu R N (p N)) :
    (∀ i, meanNumber 0 (p 0) i = 0) ∧
    (∀ (N : ℕ), 1 ≤ N → ∀ i,
      meanNumber N (p N) i =
        throughput mu N (p N) i * ((1 + meanNumber (N - 1) (p (N - 1)) i) / mu i)) ∧
    (∀ (v : Fin k → ℝ) (l : Fin k), IsVisitRatio R v → v l = 1 →
      ∀ (N : ℕ), 1 ≤ N →
        throughput mu N (p N) l =
            (N : ℝ) / ∑ i, v i * ((1 + meanNumber (N - 1) (p (N - 1)) i) / mu i) ∧
          ∀ i, throughput mu N (p N) i = throughput mu N (p N) l * v i) := by sorry

end QueueingFundamentals.Networks
