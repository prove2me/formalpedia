-- Prove2me | Theorems.Thm_VapnikChervonenkis_Inequality_semisample_deviation_bound
-- name    : VapnikChervonenkis.Inequality.semisample_deviation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:18:49.742756+00:00
-- url     : https://prove2.me/theorems/cfb584e3-74bc-4311-a778-bb057ee1214a
-- title:
--   $P\{\rho^{(l)} \ge \varepsilon/2\} \le 2m^S(2l)e^{-\varepsilon^2 l/8}$
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of events, and assume that the semi-sample deviation $\rho^{(l)}$ is measurable for every $l$. Let $m^S$ be the growth function of $S$. For every $l \ge 1$ and $\varepsilon > 0$, under the product law $P^{2l}$ of a double sample of size $2l$,
--   $$
--   P\Bigl\{\rho^{(l)} \ge \frac{\varepsilon}{2}\Bigr\} \le 2\, m^S(2l)\, e^{-\varepsilon^2 l / 8}.
--   $$
--
--   Combined with the symmetrization of Lemma 2, this is the estimate from which Theorem 2 follows. It holds for every $l \ge 1$, with no lower bound on $l$ in terms of $\varepsilon$.
--
--   **Formalization Note** The probability is a value in $[0, \infty]$ and the real bound enters through `ENNReal.ofReal`. The measurability of $\rho^{(l)}$ is the paper's standing assumption (p. 268, "Throughout the following we shall assume that $\rho^{(l)}$ is a measurable function").
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 271, display after 'Substituting this estimate in the integral (11), we obtain' (proof of Theorem 2)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Inequality

/-- **The bound for the semi-sample deviation** (p. 271, obtained by substituting the
permutation bound into (11)): `P{ρ^(l) ≥ ε/2} ≤ 2 m^S(2l) e^{−ε² l / 8}`. No condition
`l ≥ 2/ε²` is needed here. -/
theorem semisample_deviation_bound {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l)) (ε : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hε : 0 < ε) :
    Measure.pi (fun _ : Fin (l + l) => P) {x | ε / 2 ≤ Shared.semiSampleDeviation S l x}
      ≤ ENNReal.ofReal (2 * (Shared.growthFunction S (2 * l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) := by sorry

end VapnikChervonenkis.Inequality
