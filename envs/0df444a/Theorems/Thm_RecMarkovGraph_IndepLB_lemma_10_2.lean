-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_lemma_10_2
-- name    : RecMarkovGraph.IndepLB.lemma_10_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:46.898739+00:00
-- url     : https://prove2.me/theorems/5dac3b0f-eab8-45ff-a196-52191b6a4c46
-- title:
--   Lemma 10.2, p. 28 — if X_n ≥ 0 has mean μ_n ∈ (0,∞) and variance σ_n² = o(μ_n²), then X_n/μ_n concentrates to 1
-- statement:
--   Let $X_1,X_2,\dots$ be random variables on one probability space with $X_n\ge0$ almost surely and mean $\mu_n=\mathbb E X_n\in(0,\infty)$, and with variance $\sigma_n^2$ finite for all large $n$. If $\sigma_n^2=o(\mu_n^2)$ as $n\to\infty$, then $X_n/\mu_n$ concentrates to $1$: for every $\varepsilon>0$,
--   $$\lim_{n\to\infty}\mathbb P\Bigl\{\Bigl|\frac{X_n}{\mu_n}-1\Bigr|\le\varepsilon\Bigr\}=1 .$$
--
--   This is the step from the second-moment ratio of Lemma 10.4 to convergence in probability of $S_n/\mathbb E S_n$.
--
--   Differences from the source:
--   - generalization: "the variance σ_n² of X_n" with σ_n² = o(μ_n²), so σ_n² finite for all large n; random variables → MemLp (X n) 2 P for all large n (∀ᶠ n in atTop) and Measurable (X n); σ_n² = ProbabilityTheory.variance (X n) P; reason: σ_n² = o(μ_n²) forces a finite variance only eventually, and the conclusion is a limit; at the finitely many n with infinite variance Lean's variance is the junk value 0, which an eventual o-condition ignores; specializes to the source, where every σ_n² may be finite
--   - encoding: μ_n ∈ (0, ∞); σ_n² = o(μ_n²) → 0 < ∫ X n ∂P; (fun n => variance (X n) P) =o[atTop] (fun n => (∫ X n ∂P)^2); reason: the mean of an integrable variable is finite; Landau o as Asymptotics.IsLittleO
--   - encoding: ξ_n concentrates to c: P{|ξ_n − c| ⩽ ε} → 1 for every ε > 0 (p. 4) → ∀ ε > 0, Tendsto (fun n => P{|ξ_n − c| ≤ ε}) atTop (𝓝 1); reason: the paper's own definition, with ≤ ε
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 28, Lemma 10.2

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_10_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n, 0 ≤ᵐ[P] X n)
    (hX2 : ∀ᶠ n in atTop, MemLp (X n) 2 P) (hμ : ∀ n, 0 < ∫ ω, X n ω ∂P)
    (hσ : (fun n => variance (X n) P) =o[atTop] (fun n => (∫ ω, X n ω ∂P) ^ 2)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | |X n ω / ∫ ω', X n ω' ∂P - 1| ≤ ε}) atTop (𝓝 1) := by sorry

end RecMarkovGraph.IndepLB
