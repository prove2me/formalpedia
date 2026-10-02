-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_lemma2_symmetrization
-- name    : VapnikChervonenkis.Entropy.lemma2_symmetrization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:07:22.13199+00:00
-- url     : https://prove2.me/theorems/da50bf12-7a7c-441d-b1e5-85e28f8cb83c
-- title:
--   Lemma 2 — P(ρ^(l) ≥ ε/2) ≥ ½ P(π^(l) > ε) for l ≥ 2/ε²
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of measurable events such that $\pi^{(l)}$ and $\rho^{(l)}$ are measurable functions of the sample for every $l$. Let $\varepsilon > 0$ and $l \ge 2/\varepsilon^2$. With $Q = \{\pi^{(l)} > \varepsilon\}$, an event on samples of size $l$, and $C = \{\rho^{(l)} \ge \tfrac12 \varepsilon\}$, an event on samples of size $2l$,
--
--   $$
--   \mathbf{P}(C) \ge \tfrac12\, \mathbf{P}(Q), \qquad\text{i.e.}\qquad \mathbf{P}\{\pi^{(l)} > \varepsilon\} \le 2\, \mathbf{P}\{\rho^{(l)} \ge \tfrac12\varepsilon\} .
--   $$
--
--   This symmetrization inequality replaces the unknown probabilities $P_A$ by relative frequencies in an independent second sample; in Theorem 4 it reduces sufficiency to an estimate of $\mathbf{P}(C)$.
--
--   **Formalization Note.** Correction of the printed statement: Lemma 2 is printed for $l > 2/\varepsilon^2$; its proof (p. 269) establishes it for $l \ge 2/\varepsilon^2$, the stronger form stated here. The measurability of the events of $S$ (p. 264), of $\pi^{(l)}$ (p. 265) and of $\rho^{(l)}$ (p. 268) are the paper's own assumptions. On p. 275 the lemma is recalled as "$2\mathbf{P}(C) \ge \frac12 P(Q)$", a misprint for $\mathbf{P}(C) \ge \frac12 \mathbf{P}(Q)$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 268, Lemma 2 (condition l > 2/ε² relaxed to l ≥ 2/ε², as in its proof on p. 269)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- **Lemma 2** of Vapnik and Chervonenkis (1971), p. 268, in the form its proof establishes
(p. 269, "for l ≧ 2/ε²"): for `l ≥ 2/ε²`, `P(ρ^(l) ≥ ε/2) ≥ ½ P(π^(l) > ε)`, written as
`P(π^(l) > ε) ≤ 2 P(ρ^(l) ≥ ε/2)`. The printed statement has `l > 2/ε²`; the `≥` form is
stronger. `π^(l)` lives on samples of size `l`, `ρ^(l)` on double samples of size `2l`.
`hS`, `hπ`, `hρ` are the paper's standing assumptions (pp. 264, 265, 268). -/
theorem lemma2_symmetrization {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (ε : ℝ) (l : ℕ) (hε : 0 < ε) (hl : 2 / ε ^ 2 ≤ (l : ℝ)) :
    Measure.pi (fun _ : Fin l => P) {x | ε < Shared.maxDeviation S P l x}
      ≤ 2 * Measure.pi (fun _ : Fin (l + l) => P)
          {x | ε / 2 ≤ Shared.semiSampleDeviation S l x} := by sorry

end VapnikChervonenkis.Entropy
