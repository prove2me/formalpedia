-- Prove2me | Theorems.Thm_WasteNotWant_lemma_1
-- name    : WasteNotWant.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:40.290386+00:00
-- url     : https://prove2.me/theorems/70e8e777-3fb7-4058-88fe-2310d9a253e8
-- title:
--   Lemma 1 — the quick response optimum and the threshold $\bar\delta^Q$
-- statement:
--   Let $\mu$ be a market law on $[a,b]$ with cdf $F$, let $\delta>0$, and let
--   $$\bar\delta^Q=\Bigl(\frac{p_f}{c_m+c}-1\Bigr)\cdot c.$$
--
--   1. If $\delta<\bar\delta^Q$, a pair $(x,q)$ is optimal in the quick response model if and only if
--   $$F\Bigl(\frac{x}{1-p_f}\Bigr)=1-\frac{c_m}{p_f-c-\delta}\qquad\text{and}\qquad F\Bigl(\frac{q}{1-p_f}\Bigr)=1-\frac{c}{c+\delta}.$$
--   An optimal pair exists, and every optimal pair satisfies $q<x$ and $\mathbb E\,q^Q_\delta(x,q,Y)>0$.
--
--   2. If $\delta\ge\bar\delta^Q$, a pair $(x,q)$ is optimal in the quick response model if and only if
--   $$F\Bigl(\frac{x}{1-p_f}\Bigr)=1-\frac{c_m+c}{p_f}\qquad\text{and}\qquad q=x.$$
--   An optimal pair exists, and every optimal pair satisfies $q^Q_\delta(x,q,y)=0$ for all $y$.
--
--   Below the threshold the firm holds spare fabric and uses quick response. At or above it the firm behaves as in the benchmark model.
--
--   **Formalization Note** The threshold is the explicit quantity above, a definition of the model. Under the standing assumptions $\bar\delta^Q<p_f-c-c_m$, so the denominator in case 1 is positive.
--
--   Differences from the source:
--   - reading: market size with cdf F on support [a, b] → law μ with cdf F = cdf μ: probability measure carried by [a, b], positive on every open subinterval, no atoms, 0 ≤ a < b; reason: the fractile equations with levels in (0, 1) presuppose a continuous, strictly increasing F; Y is a number of consumers, and a = b would be an atom
--   - reading: p_f > c + c_m → p_f > c + c_m together with p_f < 1, c_m > 0, c ≥ 0; reason: valuations are uniform on [0, 1] and the paper divides by 1 − p_f; c and c_m are unit costs; at c_m = 0 the optimal fabric level is not unique
--   - reading: maximize subject to q ≤ x → maximize over the set 0 ≤ q ≤ x; reason: the proof on p.44 states the constraints q ≤ x, q ≥ 0, x ≥ 0
--   - reading: the optimal decisions are given by the displayed equations → a pair is optimal if and only if the equations hold, and an optimal pair exists; reason: the equations have exactly one solution under the reading of the law, so this is what the printed sentence asserts
--   - generalization: q^Q_δ(x^Q, q^Q, y) = 0 for a realization y → for every real y; reason: the statement for all real y specializes to y ∈ [a, b]
--   - encoding: there exists a threshold δ̄^Q = (p_f/(c_m + c) − 1) · c → the threshold is the defined quantity with that formula; reason: the printed existential names the formula, so nothing is lost
-- source:
--   Long–Gui, Waste Not Want Not?, SSRN 4013877 (2023-08-10 copy), Lemma 1, p.10

import Mathlib
import Definitions.Def_WasteNotWant_Model

open MeasureTheory ProbabilityTheory

namespace WasteNotWant

/-- **Lemma 1: the optimal decisions of the quick response model.**
Long–Gui, *Waste Not Want Not?*, SSRN 4013877 (2023-08-10 copy), Lemma 1, p.10. With the threshold
`δ̄^Q = (p_f / (c_m + c) - 1) · c` and `δ > 0`:

(i) if `δ < δ̄^Q`, the optimal `(x^Q, q^Q)` are given by
`F(x^Q / (1 - p_f)) = 1 - c_m / (p_f - c - δ)` and `F(q^Q / (1 - p_f)) = 1 - c / (c + δ)`, and they
satisfy `q^Q < x^Q` and `E q^Q_δ(x^Q, q^Q, Y) > 0`;

(ii) if `δ ≥ δ̄^Q`, the optimal `(x^Q, q^Q)` are given by
`F(x^Q / (1 - p_f)) = 1 - (c_m + c) / p_f` and `q^Q = x^Q`, and `q^Q_δ(x^Q, q^Q, y) = 0`.

**Formalization Note.** "Are given by" is read as: `(x, q)` is optimal if and only if the displayed
equations hold, and an optimal pair exists. In (i) the denominator `p_f - c - δ` is positive,
because `δ̄^Q < p_f - c - c_m`. Case (ii) includes `δ ≥ p_f - c`, where the stage-2 rule vanishes
identically. In (ii) the stage-2 quantity is `0` for every real `y`. -/
theorem lemma_1 (P : Params) {μ : Measure ℝ} {a b : ℝ} (hμ : IsMarketLaw μ a b)
    {δ : ℝ} (hδ : 0 < δ) :
    (δ < threshold P →
      (∀ x q : ℝ, IsQROptimal P μ δ x q ↔
        cdf μ (x / (1 - P.pf)) = 1 - P.cm / (P.pf - P.c - δ) ∧
        cdf μ (q / (1 - P.pf)) = 1 - P.c / (P.c + δ)) ∧
      (∃ x q : ℝ, IsQROptimal P μ δ x q) ∧
      ∀ x q : ℝ, IsQROptimal P μ δ x q → q < x ∧ 0 < ∫ y, stage2Rule P δ x q y ∂μ) ∧
    (threshold P ≤ δ →
      (∀ x q : ℝ, IsQROptimal P μ δ x q ↔
        cdf μ (x / (1 - P.pf)) = 1 - (P.cm + P.c) / P.pf ∧ q = x) ∧
      (∃ x q : ℝ, IsQROptimal P μ δ x q) ∧
      ∀ x q : ℝ, IsQROptimal P μ δ x q → ∀ y : ℝ, stage2Rule P δ x q y = 0) := by sorry

end WasteNotWant
