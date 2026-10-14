-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_1
-- name    : PeriodicMAB.Upper.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:43.029293+00:00
-- url     : https://prove2.me/theorems/02a3bdec-74a9-4a6e-97c2-16cf1d6791d4
-- title:
--   Lemma 1, p. 17 — $P(\sup_{v\in[0,1/2]}|\tilde\epsilon_k(v)|\ge\delta)\le 48n\exp(-(n\delta^2/4\sigma^2)(1-\pi/24)^2)$
-- statement:
--   Let the noises $\epsilon_t$ satisfy Assumption 2 with parameter $\sigma>0$, let $n\ge1$, and let $\tilde\epsilon_k(v)=\frac1n\sum_{s=nk+1}^{n(k+1)}\epsilon_s e^{-2\pi ivs}$ be the DFT of the noise over the stage-one block of arm $k$. For every $\delta>0$,
--   $$
--   \mathbb P\Big(\sup_{v\in[0,1/2]}|\tilde\epsilon_k(v)|\ge\delta\Big)\le 48n\exp\Big(-\frac{n\delta^2}{4\sigma^2}\Big(1-\frac{\pi}{24}\Big)^2\Big).
--   $$
--
--   The bound controls the noise in the periodogram uniformly over the whole frequency window; with $\delta=\bar\epsilon_v$ it gives the threshold's failure probability $48/n^{H^2-1}$ used by Lemmas 4 and 5.
--
--   **Formalization Note** "$\sup\ge\delta$" is written as the event that some $v\in[0,1/2]$ has $|\tilde\epsilon_k(v)|\ge\delta$; the probability of a set is its outer measure, so no measurability is presupposed. Arms are 0-based (the paper's arm $k$ is block index $k-1$); the statement is made for every block index $k\in\mathbb N$, which contains every arm.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 17, Lemma 1

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 1 (p. 17): for the stage-one block of (0-based) arm index `k` and any `δ > 0`,
`P(sup_{v ∈ [0,1/2]} |ε̃_k(v)| ≥ δ) ≤ 48 n exp(−(nδ²/(4σ²))(1 − π/24)²)`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hε : IsSubGaussianNoise P ε σ)
    (n k : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    P {ω | ∃ v ∈ Set.Icc (0 : ℝ) (1 / 2), δ ≤ ‖epsTilde ε n k v ω‖} ≤
      ENNReal.ofReal (48 * n * Real.exp (-(n * δ ^ 2 / (4 * (σ : ℝ) ^ 2)) * (1 - Real.pi / 24) ^ 2)) := by sorry

end PeriodicMAB.Upper
