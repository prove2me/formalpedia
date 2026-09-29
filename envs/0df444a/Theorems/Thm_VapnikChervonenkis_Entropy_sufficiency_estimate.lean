-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_sufficiency_estimate
-- name    : VapnikChervonenkis.Entropy.sufficiency_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:08:14.32069+00:00
-- url     : https://prove2.me/theorems/072d5e93-f5ac-4506-9f82-e408a83b7047
-- title:
--   Sufficiency estimate — P(C) ≤ 2(2/e)^{ε²l/8} + P⁺(2l, ε²/16)
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of subsets of $X$ such that $\rho^{(l)}$ and the index $\Delta^S$ are measurable functions of the sample for every $l$. Let $\varepsilon > 0$, $l \ge 1$, and $\delta = \varepsilon^2/16$. For independent samples $x_1, \dots, x_{2l}$ from $P$,
--
--   $$
--   \mathbf{P}\Bigl\{\rho^{(l)} \ge \frac{\varepsilon}{2}\Bigr\} \le 2 \Bigl(\frac{2}{e}\Bigr)^{\varepsilon^2 l/8} + \mathbf{P}\Bigl\{ \frac{1}{2l} \log_2 \Delta^S(x_1, \dots, x_{2l}) > \delta \Bigr\} .
--   $$
--
--   The first term is $2 \cdot 2^{2\delta l} e^{-\varepsilon^2 l/8}$ and tends to $0$ since $2/e < 1$; the second term, $P^+(2l, \delta)$ in the paper's notation with $c = 0$, tends to $0$ by Lemma 4 when $H^S(l)/l \to 0$. With Lemma 2 this proves the sufficiency half of Theorem 4.
--
--   **Formalization Note.** The estimate is stated for every class $S$, without assuming $H^S(l)/l \to 0$. The measurability of $\rho^{(l)}$ (p. 268) and of the index (p. 273) are the paper's own assumptions. The paper writes the integration region as $\{\log_2 \Delta^S(X_{2l}) \le 2\delta\}$, a misprint for $\{\log_2 \Delta^S(X_{2l}) \le 2\delta l\}$ (the next line uses $\Delta^S \le 2^{2\delta l}$ on it). Probabilities are real numbers here (`Measure.real`), and the power $(2/e)^{\varepsilon^2 l/8}$ has a real exponent.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 276, proof of sufficiency of Theorem 4 (display after "Using the fact that Δ^S(x_1, ···, x_{2l}) ≦ 2^{2δl}")

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- **The sufficiency estimate** of Theorem 4 (p. 276): with `δ = ε²/16`,
`P(C) ≤ 2·2^{2δl} e^{−ε²l/8} + P⁺(2l, δ) = 2(2/e)^{ε²l/8} + P⁺(2l, δ)`, where
`C = {ρ^(l) ≥ ε/2}` and `P⁺(2l, δ)` is the probability that
`(2l)⁻¹ log₂ Δ^S(x_1, …, x_{2l}) > δ` (the sufficiency proof takes `c = 0`). The estimate holds
for every class `S`; `hρ` and `hΔ` are the paper's measurability assumptions (pp. 268, 273). -/
theorem sufficiency_estimate {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x))
    (ε : ℝ) (l : ℕ) (hε : 0 < ε) (hl : 1 ≤ l) :
    (Measure.pi (fun _ : Fin (l + l) => P)).real {x | ε / 2 ≤ Shared.semiSampleDeviation S l x}
      ≤ 2 * (2 / Real.exp 1) ^ (ε ^ 2 * l / 8)
        + (Measure.pi (fun _ : Fin (l + l) => P)).real
            {x | ε ^ 2 / 16 < Real.logb 2 (Shared.index S x : ℝ) / (2 * (l : ℝ))} := by sorry

end VapnikChervonenkis.Entropy
