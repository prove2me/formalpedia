-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_theorem4_entropy_criterion
-- name    : VapnikChervonenkis.Entropy.theorem4_entropy_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:10:44.976984+00:00
-- url     : https://prove2.me/theorems/99227a43-d269-47de-9aa3-8adadd7e3e00
-- title:
--   Theorem 4 — uniform convergence in probability iff H^S(l)/l → 0
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of measurable events. For an independent sample $x_1, \dots, x_l$ from $P$ let
--
--   $$
--   \pi^{(l)} = \sup_{A \in S} \bigl|\nu_A^{(l)} - P_A\bigr|
--   $$
--
--   be the largest deviation of a relative frequency from its probability, and let $H^S(l) = \mathbf{E} \log_2 \Delta^S(x_1, \dots, x_l)$ be the entropy of $S$ in samples of size $l$. Assume, as the paper does, that $\pi^{(l)}$, the semi-sample deviation $\rho^{(l)}$ and the index $\Delta^S$ are measurable functions of the sample. Then the relative frequencies converge in probability to the probabilities uniformly over $S$, that is,
--
--   $$
--   \lim_{l \to \infty} \mathbf{P}\{\pi^{(l)} > \varepsilon\} = 0 \quad\text{for every } \varepsilon > 0,
--   $$
--
--   if and only if
--
--   $$
--   \lim_{l \to \infty} \frac{H^S(l)}{l} = 0 . \tag{21}
--   $$
--
--   Unlike the distribution-free sufficient condition through the growth function (Theorem 2), this criterion depends on $P$ and is both necessary and sufficient.
--
--   **Formalization Note.** Samples are functions `Fin l → X` with the product law `Measure.pi`; probabilities are values in $[0, \infty]$. The four measurability hypotheses are the paper's standing assumptions: the events of $S$ are measurable (p. 264), $\pi^{(l)}$ is a random variable (p. 265), $\rho^{(l)}$ is measurable (p. 268), and the index is measurable (p. 273).
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 275, Theorem 4, Eq. (21)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_deviation
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- **Theorem 4** of Vapnik and Chervonenkis (1971), p. 275: a necessary and sufficient condition
for the relative frequencies to converge (in probability) to the probabilities uniformly over the
class of events `S`, i.e. `P{π^(l) > ε} → 0` for every `ε > 0` (p. 265), is that (21)
`lim_{l→∞} H^S(l)/l = 0`. `hS`, `hπ`, `hρ`, `hΔ` are the paper's standing assumptions: the events
of `S` are measurable (p. 264), and `π^(l)` (p. 265), `ρ^(l)` (p. 268) and the index `Δ^S`
(p. 273) are measurable functions of the sample. -/
theorem theorem4_entropy_criterion {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
        {x | ε < Shared.maxDeviation S P l x}) atTop (𝓝 0))
      ↔ Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 0) := by sorry

end VapnikChervonenkis.Entropy
