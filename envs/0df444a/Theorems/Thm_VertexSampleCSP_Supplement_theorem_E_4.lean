-- Prove2me | Theorems.Thm_VertexSampleCSP_Supplement_theorem_E_4
-- name    : VertexSampleCSP.Supplement.theorem_E_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:01:06.068603+00:00
-- url     : https://prove2.me/theorems/c2152dd8-c3e8-456b-8f5e-416e013a1e2b
-- title:
--   Theorem E.4 — lower bound at every density: $k\le c''_r n^r/(\varepsilon^2m_0)$ samples fail to estimate $\mathrm{OPT}$ within $\varepsilon m$
-- statement:
--   Let $r\ge2$ and $c''_r=5\cdot10^{-4}/(4^{r-1}(r-1)!)$, let $0<\varepsilon\le 1/16$ and $n\ge 4r$, and let $t$ be an integer with $3\varepsilon^{-2}\le t\le n/2$. Put $m_0=t\binom{n-t}{r-1}$. For every natural number
--   $$k\le\frac{c''_r\,n^r}{\varepsilon^2m_0}$$
--   and every (possibly randomized) algorithm that receives the subinstance induced on a uniformly random set of $k$ distinct vertices out of $n$ and outputs a number, there is an $r$-uniform hypergraph on the $n$ vertices with $m$ edges, $3m_0/16\le m\le 13m_0/16$, whose Max-Cut instance $\mathcal I$ satisfies
--   $$\Pr\Big[\,|\text{output}-\mathrm{OPT}(\mathcal I)|>\varepsilon m\Big]>\frac13 .$$
--
--   The sample size $O(n^r/(\varepsilon^2 m))$ that Theorem 1.1 gives for error $\varepsilon m$ is therefore necessary at every density at which it is below a small constant multiple of $n$.
--
--   **Formalization Note** The algorithm is its output law given the observation and is fixed before the hypergraph. The hypotheses imply $k\le n$, so the failure probability is a genuine probability.
--
--   Differences from the source:
--
--   - encoding: an algorithm with sample size k, possibly using additional randomness → A : SampleAlgorithm (Fin n) r 2, a probability law on ℝ for each sampled set S and subinstance I[S]; failure probability failProb k A I τ; reason: the algorithm's extra randomness is independent of the sample, so it is its output law given the observation; deterministic algorithms are Dirac laws
--   - encoding: an instance I of Max-Cut on an r-uniform hypergraph with m edges → maxCutInstance r E for E : Finset (Finset (Fin n)) with every edge of card r, m = E.card; reason: same instances; for r ≥ 2 the number of edges is the number of constraints
--   - encoding: t an integer, m_0 = t·binom(n−t, r−1) → t : ℕ, m_0 = t * (n - t).choose (r - 1) with truncated subtraction; reason: t ≥ 3ε^{−2} > 0 and t ≤ n/2, so t is a natural number and n − t is exact
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem E.4, pp.21–22 (PDF pp.23–24)

import Mathlib
import Definitions.Def_VertexSampleCSP_Supplement_maxCutInstance
import Definitions.Def_VertexSampleCSP_Supplement_SampleAlgorithm

namespace VertexSampleCSP.Supplement

/-- **Theorem E.4 (Lower bound at every density).** Chang, *Optimal Vertex Sampling for Constraint
Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem E.4, pp.21–22
(PDF pp.23–24): "Let r ≥ 2 and c″_r = 5·10^{−4}/(4^{r−1}(r − 1)!), let 0 < ε ≤ 1/16 and n ≥ 4r, and
let t be an integer with 3ε^{−2} ≤ t ≤ n/2. Put m_0 = t·binom(n−t, r−1). For every algorithm that
receives the induced subinstance on k ≤ c″_r n^r/(ε^2 m_0) uniformly random distinct variables and
outputs a number, there is an instance I of Max-Cut on an r-uniform hypergraph with
3m_0/16 ≤ m ≤ 13m_0/16 edges on which the output differs from OPT(I) by more than εm with
probability greater than 1/3."

**Formalization Note.** The vertices are `Fin n` and the instance is `maxCutInstance r E` for an
`r`-uniform edge family `E`, whose number of edges is `m = E.card`. The algorithm is a
`SampleAlgorithm (Fin n) r 2` (randomized: it returns the law of its output) with sample size `k`,
quantified before the instance. The constant `c″_r` is written out. `t` is a natural number, so
`n − t` is truncated subtraction, which is exact here because `t ≤ n/2`. The hypotheses imply
`k ≤ n`, so the uniform `k`-subset average is a genuine probability. -/
theorem theorem_E_4 (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16)
    (n : ℕ) (hn : 4 * r ≤ n) (t : ℕ) (ht : 3 / ε ^ 2 ≤ (t : ℝ)) (ht' : (t : ℝ) ≤ (n : ℝ) / 2)
    (k : ℕ)
    (hk : (k : ℝ) ≤ (5 / 10000 : ℝ) / (4 ^ (r - 1) * ((r - 1).factorial : ℝ)) * (n : ℝ) ^ r /
      (ε ^ 2 * ((t * (n - t).choose (r - 1) : ℕ) : ℝ)))
    (A : SampleAlgorithm (Fin n) r 2) :
    ∃ E : Finset (Finset (Fin n)), (∀ e ∈ E, e.card = r) ∧
      3 * ((t * (n - t).choose (r - 1) : ℕ) : ℝ) / 16 ≤ (E.card : ℝ) ∧
      (E.card : ℝ) ≤ 13 * ((t * (n - t).choose (r - 1) : ℕ) : ℝ) / 16 ∧
      1 / 3 < failProb k A (maxCutInstance r E) (ε * (E.card : ℝ)) := by sorry

end VertexSampleCSP.Supplement
