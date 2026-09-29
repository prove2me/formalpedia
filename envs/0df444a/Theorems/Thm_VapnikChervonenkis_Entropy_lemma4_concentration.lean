-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_lemma4_concentration
-- name    : VapnikChervonenkis.Entropy.lemma4_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:06:57.76386+00:00
-- url     : https://prove2.me/theorems/4f69b952-4b16-435a-a8ff-28d079885baa
-- title:
--   Lemma 4 — l⁻¹ log₂ Δ^S(x_1, …, x_l) concentrates at c
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of subsets of $X$ such that the index $\Delta^S(x_1, \dots, x_l)$ is a measurable function of the sample for every $l$, and let $c = \lim_{l\to\infty} H^S(l)/l$ (Lemma 3). Consider the random variable
--
--   $$
--   \xi^{(l)} = \frac{1}{l} \log_2 \Delta^S(x_1, \dots, x_l)
--   $$
--
--   on independent samples of size $l$ from $P$. Then for every $\varepsilon > 0$,
--
--   $$
--   \lim_{l \to \infty} \mathbf{P}\bigl( |\xi^{(l)} - c| > \varepsilon \bigr) = 0 .
--   $$
--
--   The lemma upgrades convergence of the mean $H^S(l)/l$ to convergence in probability of $\xi^{(l)}$. Both directions of Theorem 4 use it.
--
--   **Formalization Note.** $c$ is taken as a hypothesis (any real number to which $H^S(l)/l$ converges), which avoids naming the limit. The measurability of the index is the paper's own assumption (p. 273). Probabilities are values of the product measure $P^l$ in $[0, \infty]$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 273, Lemma 4

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- **Lemma 4** of Vapnik and Chervonenkis (1971), p. 273: if `c` is the limit of `H^S(l)/l`
(Lemma 3), then the random variable `ξ^(l) = l⁻¹ log₂ Δ^S(x_1, ···, x_l)` concentrates at `c`:
`lim_{l→∞} P(|ξ^(l) − c| > ε) = 0` for every `ε > 0`. `hΔ` is the paper's assumption (p. 273)
that the index is a measurable function of the sample. -/
theorem lemma4_concentration {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (c : ℝ)
    (hc : Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 c)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
        {x | ε < |Real.logb 2 (Shared.index S x : ℝ) / (l : ℝ) - c|}) atTop (𝓝 0) := by sorry

end VapnikChervonenkis.Entropy
