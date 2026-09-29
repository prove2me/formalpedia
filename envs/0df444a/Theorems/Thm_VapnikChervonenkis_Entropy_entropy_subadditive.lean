-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_entropy_subadditive
-- name    : VapnikChervonenkis.Entropy.entropy_subadditive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:05:45.25545+00:00
-- url     : https://prove2.me/theorems/53c4e1fe-2bce-4b4f-bab5-781514406dd3
-- title:
--   Subadditivity of the entropy: H^S(l₁ + l₂) ≤ H^S(l₁) + H^S(l₂)
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of subsets of $X$ such that the index $\Delta^S(x_1, \dots, x_l)$ is a measurable function of the sample for every $l$. Then the entropy $H^S(l) = \mathbf{E} \log_2 \Delta^S(x_1, \dots, x_l)$ is subadditive: for all $l_1, l_2 \ge 0$,
--
--   $$
--   H^S(l_1 + l_2) \le H^S(l_1) + H^S(l_2) .
--   $$
--
--   Subadditivity is what makes $H^S(l)/l$ converge (Lemma 3).
--
--   **Formalization Note.** The measurability of the index is the paper's own assumption (p. 273: "In what follows it will be assumed that the index … is measurable with respect to the measure P").
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 273, Subsection 6 (display after "Inequality (13) implies that")

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- Vapnik and Chervonenkis (1971), p. 273, Subsection 6: "Inequality (13) implies that
`H^S(l_1 + l_2) ≤ H^S(l_1) + H^S(l_2)`." The entropy `H^S(l) = E log₂ Δ^S(x_1, …, x_l)` is
subadditive in the sample size. `hΔ` is the paper's assumption (p. 273) that the index is a
measurable function of the sample. -/
theorem entropy_subadditive {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (l₁ l₂ : ℕ) :
    entropy S P (l₁ + l₂) ≤ entropy S P l₁ + entropy S P l₂ := by sorry

end VapnikChervonenkis.Entropy
