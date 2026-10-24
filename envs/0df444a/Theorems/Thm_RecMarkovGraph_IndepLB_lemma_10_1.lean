-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_10_1
-- name    : RecMarkovGraph.IndepLB.lemma_10_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:40.28937+00:00
-- url     : https://prove2.me/theorems/aaebf3e5-0f7c-4665-8d9d-748d418bfb15
-- title:
--   Lemma 10.1, p. 27 (corrected: for the decay chain of Corollary 4.6 with β = γ; constant 1 + 2/γ for the printed 2r/γ) — E S_n² ≤ (1 + 2/γ) E S_n + (log n/γ)²
-- statement:
--   Let $r\in(0,1)$, $\gamma=1-r$, and let $Y_1,Y_2,\dots$ be a Markov chain of Bernoulli variables with
--   $$\mathbb P\{Y_{n+1}=1\mid Y_n=0\}=\mathbb P\{Y_n=1\},\qquad \mathbb P\{Y_{n+1}=1\mid Y_n=1\}=r\,\mathbb P\{Y_n=1\},$$
--   that is, the decay chain of Corollary 4.6 with $\beta=\gamma$. Let $S_n=Y_1+\dots+Y_n$. Then for every $n\ge2$,
--   $$\mathbb E S_n^2\ \le\ \Bigl(1+\frac2\gamma\Bigr)\mathbb E S_n+\Bigl(\frac{\log n}{\gamma}\Bigr)^2 .$$
--
--   Since $\mathbb E S_n\sim\log n/\gamma$, this bound gives $\mathbb E S_n^2/(\mathbb E S_n)^2\to1$ (Lemma 10.4), the second-moment input for the concentration of $S_n/\log n$.
--
--   Differences from the source:
--   - correction: §10's setting: a sequence of Bernoulli variables whose marginals obey p_n = f_β(p_{n−1}) (Theorem 4.4), with r and γ of the graph → a decay chain IsDecayChain P Y (1 − r) (Corollary 4.6 with β = γ = 1 − r), 0 < r < 1; reason: under the marginal recursion alone the lemma is false: Y_n = 1{U ≤ p_n}, U uniform, gives E S_n² ≈ 2n/β, far above (log n/γ)²; the proof uses Lemma 6.2, i.e. the Markov structure; β = 0 (γ = 0) is excluded because the bound divides by γ
--   - correction: constant 2r/γ in front of E S_n → 1 + 2/(1 − r); reason: false for the chain at small n: r = 0.05, P{Y_1 = 1} = 0.7, n = 2 gives E S_2² = 0.9835 > 0.6307; the printed proof's own chain of inequalities yields 1 + 2/γ
--   - generalization: P{Y_1 = 1} = p_1 = x_1 ∈ (0, 1) (recursion (3), p. 9) → no hypothesis on P{Y 0 = 1}; reason: at P{Y_1 = 1} = 0 the chain is 0 and the bound is trivial; at P{Y_1 = 1} = 1 it holds (exact check, n ≤ 2·10⁴); specializes to x_1 ∈ (0, 1)
--   - encoding: S_n = Y_1 + ⋯ + Y_n; E → ∑ k ∈ range n, Y k; Bochner integral ∫ · ∂P (S_n is bounded); reason: 0-based index; same numbers
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 27, Lemma 10.1 (§10.2.1, pp. 26–28)

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open MeasureTheory Finset

theorem lemma_10_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hY : IsDecayChain P Y (1 - r)) :
    ∀ n : ℕ, 2 ≤ n →
      ∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂P ≤
        (1 + 2 / (1 - r)) * ∫ ω, ∑ k ∈ range n, Y k ω ∂P + (Real.log n / (1 - r)) ^ 2 := by sorry

end RecMarkovGraph.IndepLB
