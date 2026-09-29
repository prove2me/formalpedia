-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_lemma3_entropy_rate_limit
-- name    : VapnikChervonenkis.Entropy.lemma3_entropy_rate_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:06:23.598621+00:00
-- url     : https://prove2.me/theorems/0beed8db-9f1e-4e31-a8cc-73934bb571c7
-- title:
--   Lemma 3 — H^S(l)/l has a limit c ∈ [0, 1]
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of subsets of $X$ such that the index $\Delta^S(x_1, \dots, x_l)$ is a measurable function of the sample for every $l$. Then the entropy per observation converges: there is a number $c$ with $0 \le c \le 1$ such that
--
--   $$
--   \lim_{l \to \infty} \frac{H^S(l)}{l} = c .
--   $$
--
--   The limit $c$ is the asymptotic entropy rate of the class. Theorem 4 states that uniform convergence in probability holds exactly when $c = 0$.
--
--   **Formalization Note.** The measurability of the index is the paper's own assumption (p. 273). $l$ ranges over $\mathbb{N}$ and $H^S(l)/l$ is a real quotient (its value at $l = 0$ does not affect the limit).
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 273, Lemma 3

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- **Lemma 3** of Vapnik and Chervonenkis (1971), p. 273: the sequence `H^S(l)/l` has a limit
`c` with `0 ≤ c ≤ 1` as `l → ∞`. `hΔ` is the paper's assumption (p. 273) that the index is a
measurable function of the sample. -/
theorem lemma3_entropy_rate_limit {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧
      Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 c) := by sorry

end VapnikChervonenkis.Entropy
