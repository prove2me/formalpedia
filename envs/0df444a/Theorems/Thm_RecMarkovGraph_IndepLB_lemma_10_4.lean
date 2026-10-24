-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_10_4
-- name    : RecMarkovGraph.IndepLB.lemma_10_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:44.26542+00:00
-- url     : https://prove2.me/theorems/63d3e4a5-3345-4e2a-ab21-2afaf6c60bdd
-- title:
--   Lemma 10.4, p. 28 (corrected setting: a decay chain as in Corollary 4.6, β ∈ [0, 1]) — E S_n² / (E S_n)² → 1
-- statement:
--   Let $\beta\in[0,1]$ and let $Y_1,Y_2,\dots$ be a Markov chain of Bernoulli variables with $\mathbb P\{Y_1=1\}>0$,
--   $$\mathbb P\{Y_{n+1}=1\mid Y_n=0\}=\mathbb P\{Y_n=1\},\qquad \mathbb P\{Y_{n+1}=1\mid Y_n=1\}=(1-\beta)\,\mathbb P\{Y_n=1\}.$$
--   With $S_n=Y_1+\dots+Y_n$,
--   $$\lim_{n\to\infty}\frac{\mathbb E S_n^2}{(\mathbb E S_n)^2}=1 .$$
--
--   Equivalently $\mathrm{Var}\,S_n=o((\mathbb E S_n)^2)$, which with Lemma 10.2 gives the concentration of $S_n$ around its mean.
--
--   Differences from the source:
--   - correction: §10's setting: a Bernoulli sequence whose marginals obey p_n = f_β(p_{n−1}), β ∈ (0, 1] (Theorem 4.4) → a decay chain IsDecayChain P Y β (Corollary 4.6's chain), β ∈ (0, 1] kept; reason: under the marginal recursion alone the lemma is false: the comonotone coupling Y_n = 1{U ≤ p_n} has E S_n² / (E S_n)² → ∞; the proof rests on Lemma 10.1, which needs the Markov structure
--   - generalization: β ∈ (0, 1] (Theorem 4.4) → 0 ≤ β ≤ 1; reason: β = 0 is Corollary 4.6's range and the chain is then i.i.d. Bernoulli(P{Y_1 = 1}), where E S_n² / (E S_n)² = 1 + (1 − p)/(np) → 1; specializes to β ∈ (0, 1]
--   - reading: no condition on P{Y_1 = 1} → 0 < P{Y 0 = 1}; reason: §10's sequence follows recursion (3), which assumes x_1 ∈ (0, 1) (p. 9); the chain Y ≡ 0 gives 0/0
--   - generalization: P{Y_1 = 1} = x_1 < 1 (recursion (3)) → P{Y 0 = 1} ∈ (0, 1]; reason: the statement is about the chain, and at P{Y_1 = 1} = 1 it is the same chain shifted by one step; specializes to x_1 ∈ (0, 1)
--   - encoding: S_n = Y_1 + ⋯ + Y_n; E → ∑ k ∈ range n, Y k; ∫ · ∂P; reason: 0-based index; same numbers
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 28, Lemma 10.4 (§10.2.3)

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open MeasureTheory Finset Filter Topology

theorem lemma_10_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hY : IsDecayChain P Y β)
    (hY0 : 0 < P.real {ω | Y 0 ω = 1}) :
    Tendsto (fun n : ℕ => (∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂P) /
        (∫ ω, ∑ k ∈ range n, Y k ω ∂P) ^ 2) atTop (𝓝 1) := by sorry

end RecMarkovGraph.IndepLB
