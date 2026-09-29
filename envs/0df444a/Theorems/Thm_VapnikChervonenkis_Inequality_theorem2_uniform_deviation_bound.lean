-- Prove2me | Theorems.Thm_VapnikChervonenkis_Inequality_theorem2_uniform_deviation_bound
-- name    : VapnikChervonenkis.Inequality.theorem2_uniform_deviation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:19:12.459417+00:00
-- url     : https://prove2.me/theorems/4708fd16-1a4c-43b4-b0c8-1a9d19196355
-- title:
--   Theorem 2 (VC inequality) — $P(\pi^{(l)} > \varepsilon) \le 4m^S(2l)e^{-\varepsilon^2 l/8}$ for $l \ge 2/\varepsilon^2$
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of measurable events. For a sample $x_1, \dots, x_l$ drawn from the product law $P^l$, let $\nu_A^{(l)}$ be the relative frequency of $A \in S$ and
--   $$
--   \pi^{(l)} = \sup_{A \in S} \bigl|\nu_A^{(l)} - P_A\bigr|
--   $$
--   the largest deviation of a relative frequency from its probability. Let $\rho^{(l)}$ be the largest difference of relative frequencies between the two halves of a double sample of size $2l$, and $m^S$ the growth function of $S$. Assume, as the paper does, that $\pi^{(l)}$ and $\rho^{(l)}$ are measurable for every $l$. Then for every $\varepsilon > 0$ and every sample size $l \ge 2/\varepsilon^2$,
--   $$
--   P\bigl(\pi^{(l)} > \varepsilon\bigr) \le 4\, m^S(2l)\, e^{-\varepsilon^2 l / 8}.
--   $$
--
--   The bound does not depend on $P$. Whenever the growth function grows polynomially, the right side tends to $0$, which gives uniform convergence of relative frequencies to probabilities (the Corollary and Theorem 3).
--
--   **Formalization Note** The probability is a value in $[0, \infty]$ and the real bound enters through `ENNReal.ofReal`. The hypothesis $\varepsilon > 0$ is implicit in the paper's $l \ge 2/\varepsilon^2$ and is stated; together they force $l \ge 1$. The measurability of $\pi^{(l)}$ (p. 265) and of $\rho^{(l)}$ (p. 268) are the paper's own standing assumptions; the events of $S$ are measurable (p. 264). The printed statement reads "more then $\varepsilon$" (a typo for "more than").
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 269, Theorem 2 (proof pp. 270–271)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Inequality

/-- **Theorem 2** (p. 269): for `l ≥ 2/ε²`, the probability that the relative frequency of at
least one event of `S` differs from its probability by more than `ε` in a sample of size `l`
satisfies `P(π^(l) > ε) ≤ 4 m^S(2l) e^{−ε² l / 8}`. -/
theorem theorem2_uniform_deviation_bound {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (ε : ℝ) (l : ℕ) (hε : 0 < ε) (hl : 2 / ε ^ 2 ≤ (l : ℝ)) :
    Measure.pi (fun _ : Fin l => P) {x | ε < Shared.maxDeviation S P l x}
      ≤ ENNReal.ofReal (4 * (Shared.growthFunction S (2 * l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) := by sorry

end VapnikChervonenkis.Inequality
