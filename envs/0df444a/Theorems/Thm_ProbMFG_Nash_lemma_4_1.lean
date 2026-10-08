-- Prove2me | Theorems.Thm_ProbMFG_Nash_lemma_4_1
-- name    : ProbMFG.Nash.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:32.725956+00:00
-- url     : https://prove2.me/theorems/90073d7c-d746-4ab4-9831-5c59df0b0f5b
-- title:
--   Lemma 4.1, p. 2724 — 𝔼[W₂²(μ̄^N, μ)] ≤ C N^{−2/(d+4)} for an i.i.d. sample from μ ∈ 𝒫_{d+5}(ℝ^d)
-- statement:
--   This is the Horowitz–Karandikar rate for the empirical measure in the 2-Wasserstein distance, as recalled by Carmona and Delarue.
--
--   Let $d\ge0$. There is a function $C$ of one variable such that the following holds. Let $\mu$ be a probability measure on $\mathbb R^d$ with finite moment $M_{d+5}(\mu) = (\int|x|^{d+5}d\mu)^{1/(d+5)}$, let $N\ge1$, and let $\xi_1,\dots,\xi_N$ be independent random variables with common law $\mu$ on some probability space. With $\bar\mu^N = \frac1N\sum_{i=1}^N\delta_{\xi_i}$ the empirical measure,
--   $$\mathbb E\big[W_2^2(\bar\mu^N,\mu)\big]\le C\big(M_{d+5}(\mu)\big)\,N^{-2/(d+4)}.$$
--   So the constant depends only on $d$ and $M_{d+5}(\mu)$.
--
--   The lemma converts propagation of chaos into a rate: it controls the distance between the empirical measure of the decoupled copies and their common law, and is used to obtain (4.12) and (4.20).
--
--   **Formalization Note** $W_2$ and $M_{d+5}$ take values in $[0,\infty]$ and the expectation is a lower Lebesgue integral; $W_2^2$ is compared with the real bound in $[0,\infty]$. "Any sample of size $N$ from $\mu$" is read as an i.i.d. sample. The page writes "a constant $c$" and then displays $C$; they are the same constant, here a function of $M_{d+5}(\mu)$ chosen after $d$ and before $\mu$, $N$ and the probability space. Norms are Euclidean.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2724, Lemma 4.1

import Mathlib
import Definitions.Def_ProbMFG_Nash_Game

open MeasureTheory
open scoped NNReal ENNReal
universe u

namespace ProbMFG.Nash

/-- Lemma 4.1, p. 2724 (Horowitz–Karandikar): for `μ ∈ 𝒫_{d+5}(ℝ^d)` and an i.i.d. sample of size
`N` from `μ`, `𝔼[W₂²(μ̄^N, μ)] ≤ C N^{-2/(d+4)}`, the constant depending only on `d` and
`M_{d+5}(μ)`. -/
theorem lemma_4_1 (d : ℕ) :
    ∃ C : ℝ≥0∞ → ℝ, ∀ μ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ →
      moment ((d : ℝ) + 5) μ < ⊤ →
      ∀ N : ℕ, 1 ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
      ∀ ξ : Fin N → Ω → EuclideanSpace ℝ (Fin d), (∀ i, Measurable (ξ i)) →
        ProbabilityTheory.iIndepFun ξ P → (∀ i, P.map (ξ i) = μ) →
        ∫⁻ ω, W2 (empirical (fun i => ξ i ω)) μ ^ 2 ∂P ≤
          ENNReal.ofReal (C (moment ((d : ℝ) + 5) μ) * (N : ℝ) ^ (-(2 : ℝ) / ((d : ℝ) + 4))) := by sorry

end ProbMFG.Nash
