-- Prove2me | Theorems.Thm_VertexSampleCSP_Supplement_theorem_E_1
-- name    : VertexSampleCSP.Supplement.theorem_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:00:21.126321+00:00
-- url     : https://prove2.me/theorems/a9ffe90c-1a42-4628-a241-d89e8746f733
-- title:
--   Theorem E.1 — matching lower bound: sample size $k\le 8\cdot10^{-4}/(16^{r-1}((r-1)!)^2\varepsilon^2)$ fails with probability $>1/3$
-- statement:
--   Let $r\ge2$, let
--   $$0<\varepsilon\le\frac{1}{12\cdot4^{r-1}(r-1)!},\qquad k\le\frac{8\cdot10^{-4}}{16^{r-1}((r-1)!)^2\varepsilon^2}$$
--   with $k$ a natural number. Then there is $N_0$ such that for every $n\ge N_0$ and every (possibly randomized) algorithm with sample size $k$ — one that receives a uniformly random set $S$ of $k$ of the $n$ vertices with the names of its vertices and the subinstance $\mathcal I[S]$, and outputs a real number — there is an $r$-uniform hypergraph $E$ on the $n$ vertices such that, for the Max-Cut instance $\mathcal I$ of $E$,
--   $$\Pr\Big[\,|\text{output}-\mathrm{OPT}(\mathcal I)|>\varepsilon n^r\Big]>\frac13 .$$
--
--   This is the formal version of Theorem 1.2: together with Theorem 1.1 it shows that $\Theta(\varepsilon^{-2})$ sampled variables are necessary and sufficient for error $\varepsilon n^r$ at constant confidence.
--
--   **Formalization Note** The algorithm is its output law given the observation, so randomized algorithms are covered. $N_0$ is chosen before the algorithm and may depend on $r,\varepsilon,k$ only; the hypergraph is chosen after the algorithm.
--
--   Differences from the source:
--
--   - encoding: an algorithm with sample size k, possibly using additional randomness → A : SampleAlgorithm (Fin n) r 2, a probability law on ℝ for each sampled set S and subinstance I[S]; failure probability failProb k A I τ; reason: the algorithm's extra randomness is independent of the sample, so it is its output law given the observation; deterministic algorithms are Dirac laws
--   - encoding: for all sufficiently large n → ∃ N₀ : ℕ, ∀ n ≥ N₀, quantified before the algorithm; reason: the standard meaning; N₀ depends on r, ε, k only, as in the proof
--   - encoding: an instance of Max-Cut on an r-uniform hypergraph with n vertices → maxCutInstance r E for E : Finset (Finset (Fin n)) with every edge of card r; reason: same instances
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem E.1 (Theorem 1.2), p.20 (PDF p.22); observation model, Appendix E, p.20; informal form Theorem 1.2, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_VertexSampleCSP_Supplement_maxCutInstance
import Definitions.Def_VertexSampleCSP_Supplement_SampleAlgorithm

namespace VertexSampleCSP.Supplement

/-- **Theorem E.1 (Theorem 1.2, matching lower bound).** Chang, *Optimal Vertex Sampling for
Constraint Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem E.1,
p.20 (PDF p.22): "Let r ≥ 2, 0 < ε ≤ 1/(12·4^{r−1}(r − 1)!), and k ≤ 8·10^{−4}/(16^{r−1}((r − 1)!)^2 ε^2).
For all sufficiently large n and every algorithm with sample size k, there is an instance of Max-Cut
on an r-uniform hypergraph with n vertices on which the output differs from the optimum by more
than εn^r with probability greater than 1/3."

**Formalization Note.** The vertices are `Fin n`. An algorithm is a `SampleAlgorithm (Fin n) r 2`:
from the sampled set `S` (with the names of its vertices) and the subinstance `I[S]` it produces the
law of its output, so randomized algorithms are covered. "For all sufficiently large n" is
`∃ N₀, ∀ n ≥ N₀`, with `N₀` chosen before the algorithm (it depends on `r`, `ε`, `k` only). The
hard instance is the Max-Cut instance `maxCutInstance r E` of an `r`-uniform edge family `E`, chosen
after the algorithm. `k` is a natural number bounded by the printed real expression (`k = 0` is
allowed). -/
theorem theorem_E_1 (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε)
    (hε' : ε ≤ 1 / (12 * 4 ^ (r - 1) * ((r - 1).factorial : ℝ)))
    (k : ℕ) (hk : (k : ℝ) ≤ (8 / 10000 : ℝ) / (16 ^ (r - 1) * ((r - 1).factorial : ℝ) ^ 2 * ε ^ 2)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ A : SampleAlgorithm (Fin n) r 2,
      ∃ E : Finset (Finset (Fin n)), (∀ e ∈ E, e.card = r) ∧
        1 / 3 < failProb k A (maxCutInstance r E) (ε * (n : ℝ) ^ r) := by sorry

end VertexSampleCSP.Supplement
