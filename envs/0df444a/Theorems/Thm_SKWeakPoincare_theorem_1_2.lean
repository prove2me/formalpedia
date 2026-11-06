-- Prove2me | Theorems.Thm_SKWeakPoincare_theorem_1_2
-- name    : SKWeakPoincare.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:31.451184+00:00
-- url     : https://prove2.me/theorems/754257dc-1d79-48da-a56a-85b4dbe8aae3
-- title:
--   Theorem 1.2 — simulated annealing (Algorithm 1) samples $\mu_A$ to TV $n^{-M}$ with probability $1-n^{-D}$ for every $\beta<1$
-- statement:
--   Fix $0\le\beta<1$ and $M,D>0$. There is a fixed integer exponent $p=p(\beta,M,D)$ such that for all sufficiently large $n$ the following holds. Algorithm 1 starts from a uniform configuration in $\{\pm1\}^n$ and performs $\lceil n^p\rceil$ heat-bath Glauber updates at each inverse temperature $\beta_j=j\beta/L$, $j=1,\dots,L$, $L=\lceil\beta n\rceil$; in total
--   $$
--   \lceil\beta n\rceil\,n^p\le n^{p+1}
--   $$
--   updates. With $P_{0,n}$-probability at least $1-n^{-D}$ over the interaction matrix $A$, the law $\hat\mu_A$ of its output satisfies
--   $$
--   d_{\mathrm{TV}}\big(\hat\mu_A,\mu_A\big)\le n^{-M}.
--   $$
--
--   So Glauber dynamics combined with simulated annealing samples the SK Gibbs measure in polynomial time with inverse-polynomial total-variation error throughout the replica-symmetric phase $\beta<1$.
--
--   **Formalization Note** $\hat\mu_A$ is the exact output law `alg1Law W β p` of Algorithm 1, $\mu_A=$ `gibbs (β • W)`, $A\sim P_{0,n}$ is `disorderLaw n`, and the event is a measurable set of disorders. At $\beta=0$ the algorithm runs no stage and returns a uniform sample, which is exact.
--
--   Differences from the source:
--   - generalization: there is a randomized algorithm that starts from uniform product spins and uses Glauber dynamics along a deterministic increasing inverse-temperature schedule → Algorithm 1 itself: schedule β_j = jβ/⌈βn⌉, n^p heat-bath updates per stage, uniform start; reason: the paper proves the guarantee for Algorithm 1 (p.43: the sampler is Algorithm 1), and the statement for this algorithm implies the existential one
--   - encoding: it runs in n^{O_{β,M,D}(1)} time → the integer p is chosen before n (depending only on β, M, D), and the run makes ⌈βn⌉·n^p ≤ n^{p+1} heat-bath updates; reason: the paper's unit-cost model (p.43) is not a machine model in Lean; each update costs O(n) operations (p.44), so the update count with p fixed is the polynomial bound
--   - encoding: produces a sample whose law is → alg1Law W β p, the exact output law (annealRun of discreteKernel); reason: annealRun multiplies the uniform law by the kernel powers in schedule order; at β = 0 there are ⌈0⌉ = 0 stages and the law is uniform, as in the proof
--   - encoding: with P_{0,n}-probability at least 1 − n^{−D} → a measurable G with disorderLaw n G ≥ 1 − n^{−D} on which the TV bound holds; reason: A ∼ P_{0,n} is Disorder n with disorderLaw n (edges i < j, zero diagonal)
--   - encoding: for all sufficiently large n → ∃ N, ∀ n ≥ N; reason: standard
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Theorem 1.2, p.3; Algorithm 1, p.44; proof p.44

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_annealRun
import Definitions.Def_SKWeakPoincare_alg1Law

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory

namespace SKWeakPoincare

/-- **Theorem 1.2 (sampling by simulated annealing).**
Hou–Liu–Yu, arXiv:2610.09882, Theorem 1.2, p. 3, for the sampler of Algorithm 1, p. 44 (proof p. 44).

Fix `0 ≤ β < 1` and `M, D > 0`. There is a fixed integer exponent `p = p(β, M, D)` such that, for all
sufficiently large `n`, Algorithm 1 (uniform start, then `⌈n^p⌉` random-scan heat-bath Glauber updates
at each inverse temperature `β_j = jβ/⌈βn⌉`, `j = 1, …, ⌈βn⌉`) makes `⌈βn⌉ n^p ≤ n^{p+1}` updates and,
with `P_{0,n}`-probability at least `1 − n^{−D}`, its output law is within `n^{−M}` total variation
of `μ_A`.

**Formalization Note.** The algorithm is Algorithm 1 itself (`alg1Law W β p`, its exact output law);
the paper's "running time `n^{O_{β,M,D}(1)}`" is recorded as `p` fixed before `n` together with the
update count `⌈βn⌉·n^p ≤ n^{p+1}` (each update is `O(n)` unit-cost operations, p. 44). At `β = 0` the
algorithm has no stage and returns a uniform sample, which is `μ_A` at `β = 0`. `A` is
`W : Disorder n` with law `disorderLaw n = P_{0,n}`, `μ_A = gibbs (β • W)`, and `lawTV` is
`½ Σ_x |p(x) − q(x)|`. The event is a measurable set `G` of disorders. -/
theorem theorem_1_2 (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (M D : ℝ) (hM : 0 < M) (hD : 0 < D) :
    ∃ p N : ℕ, ∀ n : ℕ, N ≤ n →
      alg1Stages β n * n ^ p ≤ n ^ (p + 1) ∧
      ∃ G : Set (Disorder n), MeasurableSet G ∧
        ENNReal.ofReal (1 - (n : ℝ) ^ (-D)) ≤ disorderLaw n G ∧
        ∀ W ∈ G, lawTV (alg1Law W β p) (gibbs (β • W)) ≤ (n : ℝ) ^ (-M) := by sorry

end SKWeakPoincare
