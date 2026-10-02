-- Prove2me | Theorems.Thm_VapnikChervonenkis_Inequality_lemma2_symmetrization
-- name    : VapnikChervonenkis.Inequality.lemma2_symmetrization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:16:28.90836+00:00
-- url     : https://prove2.me/theorems/9d2e6c2e-e023-4c1b-b40b-4880f6809b33
-- title:
--   Lemma 2 — $P(\rho^{(l)} \ge \varepsilon/2) \ge \tfrac12 P(\pi^{(l)} > \varepsilon)$ for $l \ge 2/\varepsilon^2$
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of measurable events. Assume, as the paper does, that the uniform deviation $\pi^{(l)}$ on samples of size $l$ and the semi-sample deviation $\rho^{(l)}$ on double samples of size $2l$ are measurable functions for every $l$. Samples of size $l$ carry the product law $P^l$, double samples the product law $P^{2l}$. Write
--   $$
--   Q = \{\pi^{(l)} > \varepsilon\}, \qquad C = \{\rho^{(l)} \ge \tfrac12 \varepsilon\}.
--   $$
--   If $\varepsilon > 0$ and $l \ge 2/\varepsilon^2$, then
--   $$
--   P(C) \ge \tfrac12\, P(Q).
--   $$
--
--   This is the symmetrization step: it replaces the unknown probabilities $P_A$ by the frequencies in an independent second semi-sample, so that the probability of a large uniform deviation is controlled by an event that depends on the sample alone.
--
--   **Formalization Note** The statement is written as $P^l(Q) \le 2\, P^{2l}(C)$ in $[0, \infty]$. The printed lemma assumes $l > 2/\varepsilon^2$, but its proof concludes "for $l \ge 2/\varepsilon^2$, $P(C) \ge \tfrac12 P(Q)$" and Theorem 2 uses the case $l = 2/\varepsilon^2$; the $\ge$ form stated here is the stronger one (a labelled correction). The measurability of $\pi^{(l)}$ (p. 265, "We shall assume that this function is measurable") and of $\rho^{(l)}$ (p. 268, "Throughout the following we shall assume that $\rho^{(l)}$ is a measurable function") are the paper's own standing assumptions.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 268, Lemma 2 (proof concludes on p. 269)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Inequality

/-- **Lemma 2** (p. 268), in the form its proof establishes (p. 269, "for l ≧ 2/ε²"):
for `l ≥ 2/ε²`, `P(ρ^(l) ≥ ε/2) ≥ ½ P(π^(l) > ε)`, written as
`P(π^(l) > ε) ≤ 2 P(ρ^(l) ≥ ε/2)`. The printed statement has `l > 2/ε²`; the `≥` form is
stronger. `π^(l)` lives on samples of size `l`, `ρ^(l)` on double samples of size `2l`. -/
theorem lemma2_symmetrization {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (ε : ℝ) (l : ℕ) (hε : 0 < ε) (hl : 2 / ε ^ 2 ≤ (l : ℝ)) :
    Measure.pi (fun _ : Fin l => P) {x | ε < Shared.maxDeviation S P l x}
      ≤ 2 * Measure.pi (fun _ : Fin (l + l) => P) {x | ε / 2 ≤ Shared.semiSampleDeviation S l x} := by sorry

end VapnikChervonenkis.Inequality
