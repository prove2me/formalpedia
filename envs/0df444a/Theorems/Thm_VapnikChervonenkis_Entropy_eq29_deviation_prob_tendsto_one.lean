-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_eq29_deviation_prob_tendsto_one
-- name    : VapnikChervonenkis.Entropy.eq29_deviation_prob_tendsto_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:10:16.805329+00:00
-- url     : https://prove2.me/theorems/03907f9d-8646-4cc5-a8cf-bb65e6e103c4
-- title:
--   (29) — P{π^(l) > ε} → 1 for ε < q/7 and q log₂(2e/q) < c
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of subsets of $X$ such that $\pi^{(l)}$, $\rho^{(l)}$ and the index $\Delta^S$ are measurable functions of the sample for every $l$. Suppose $H^S(l)/l \to c$, and let $q$ and $\varepsilon$ satisfy
--
--   $$
--   0 < q < \tfrac14, \qquad q \log_2 \frac{2e}{q} < c, \qquad 0 < \varepsilon < \frac{q}{7} .
--   $$
--
--   Then
--
--   $$
--   \lim_{l \to \infty} \mathbf{P}\Bigl\{\sup_{A \in S} |\nu_A^{(l)} - P_A| > \varepsilon\Bigr\} = 1 .
--   $$
--
--   This is the necessity half of Theorem 4 in quantitative form: if $c > 0$, one can choose such $q$ and $\varepsilon$, and then the maximal deviation exceeds $\varepsilon$ with probability tending to one, so uniform convergence in probability fails.
--
--   **Formalization Note.** The standing choice $0 < q < \frac14$ of step 2° (p. 277) is kept as a hypothesis. The measurability of $\pi^{(l)}$ (p. 265), $\rho^{(l)}$ (p. 268) and the index (p. 273) are the paper's own assumptions.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 280, proof of necessity of Theorem 4, Eq. (29) (with (28) and (25))

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_deviation
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- Display (29) at the end of the proof of necessity in Theorem 4 (p. 280): let `c` be the limit
of `H^S(l)/l`, and let `0 < q < 1/4` (the choice of step 2°, p. 277) and `ε > 0` satisfy
`ε < q/7` and `q log₂(2e/q) < c`. Then `lim_{l→∞} P{sup_{A∈S} |ν_A^l − P_A| > ε} = 1`.
`hπ`, `hρ`, `hΔ` are the paper's measurability assumptions (pp. 265, 268, 273). -/
theorem eq29_deviation_prob_tendsto_one {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (c q ε : ℝ)
    (hc : Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 c))
    (hq0 : 0 < q) (hq : q < 1 / 4) (h25 : q * Real.logb 2 (2 * Real.exp 1 / q) < c)
    (hε : 0 < ε) (hεq : ε < q / 7) :
    Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
        {x | ε < Shared.maxDeviation S P l x}) atTop (𝓝 1) := by sorry

end VapnikChervonenkis.Entropy
