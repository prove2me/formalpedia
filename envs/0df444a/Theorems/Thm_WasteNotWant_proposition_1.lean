-- Prove2me | Theorems.Thm_WasteNotWant_proposition_1
-- name    : WasteNotWant.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:46.81978+00:00
-- url     : https://prove2.me/theorems/60b2057b-b2d6-4c08-9b75-74650d43ed61
-- title:
--   Proposition 1 — more fabric and fewer units in stage 1, monotonically in $\delta$
-- statement:
--   Let $\mu$ be a market law on $[a,b]$. For every $\delta>0$, every optimal $(x^Q,q^Q)$ of the quick response model at $\delta$ and every optimal $(x^B,q^B)$ of the benchmark model,
--   $$x^Q\ge x^B\qquad\text{and}\qquad q^Q\le q^B.$$
--   Moreover, for $0<\delta_1\le\delta_2$ and optimal pairs $(x_1,q_1)$ at $\delta_1$ and $(x_2,q_2)$ at $\delta_2$,
--   $$x_1\ge x_2\qquad\text{and}\qquad q_1\le q_2,$$
--   and both inequalities are strict when $\delta_1<\delta_2$ and $\delta_1<\bar\delta^Q$.
--
--   Quick response changes the form of inventory, from finished goods to fabric, and it raises the total fabric purchased. This is the upstream effect behind the deadstock comparison of Proposition 2.
--
--   Differences from the source:
--   - reading: market size with cdf F on support [a, b] → law μ with cdf F = cdf μ: probability measure carried by [a, b], positive on every open subinterval, no atoms, 0 ≤ a < b; reason: the fractile equations with levels in (0, 1) presuppose a continuous, strictly increasing F; Y is a number of consumers, and a = b would be an atom
--   - reading: p_f > c + c_m → p_f > c + c_m together with p_f < 1, c_m > 0, c ≥ 0; reason: valuations are uniform on [0, 1] and the paper divides by 1 − p_f; c and c_m are unit costs; at c_m = 0 the optimal fabric level is not unique
--   - reading: maximize subject to q ≤ x → maximize over the set 0 ≤ q ≤ x; reason: the proof on p.44 states the constraints q ≤ x, q ≥ 0, x ≥ 0
--   - reading: as δ decreases, the quantities increase or decrease → weak monotonicity over all 0 < δ₁ ≤ δ₂; reason: the quantities are constant on [δ̄^Q, ∞) by Lemma 1(ii)
--   - generalization: no strictness claim in the statement → additionally strict for δ₁ < δ₂ with δ₁ < δ̄^Q; reason: these are the derivative signs of the proof on p.45; the weak claim is the conjunct above
--   - encoding: x^Q, q^Q, x^B, q^B written as functions of δ → statement for every optimal pair; reason: the optimizer is unique under the readings, by Lemma 1 and the benchmark characterization
-- source:
--   Long–Gui, Waste Not Want Not?, SSRN 4013877 (2023-08-10 copy), Proposition 1, p.11

import Mathlib
import Definitions.Def_WasteNotWant_Model

open MeasureTheory

namespace WasteNotWant

/-- **Proposition 1: quick response means more fabric and fewer units in stage 1.**
Long–Gui, *Waste Not Want Not?*, SSRN 4013877 (2023-08-10 copy), Proposition 1, p.11:
`x^Q ≥ x^B` and `q^Q ≤ q^B`, and as `δ` decreases, `x^Q` increases and `q^Q` decreases.

**Formalization Note.** The claims are stated for every optimal pair (the optimizer is unique under
`IsMarketLaw`, by `lemma_1`, whose existence clause also shows they are not vacuous). Over all
`δ > 0` the monotonicity is weak, since both quantities are constant on `[δ̄^Q, ∞)` by Lemma 1(ii).
The last clause adds strictness for `δ₁ < δ₂` with `δ₁ < δ̄^Q`, which is the sign of the derivatives
in the proof on p.45. -/
theorem proposition_1 (P : Params) {μ : Measure ℝ} {a b : ℝ} (hμ : IsMarketLaw μ a b) :
    (∀ δ xQ qQ xB qB : ℝ, 0 < δ → IsQROptimal P μ δ xQ qQ → IsBenchmarkOptimal P μ xB qB →
      xB ≤ xQ ∧ qQ ≤ qB) ∧
    (∀ δ₁ δ₂ x₁ q₁ x₂ q₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
      IsQROptimal P μ δ₁ x₁ q₁ → IsQROptimal P μ δ₂ x₂ q₂ →
      x₂ ≤ x₁ ∧ q₁ ≤ q₂ ∧ (δ₁ < δ₂ → δ₁ < threshold P → x₂ < x₁ ∧ q₁ < q₂)) := by sorry

end WasteNotWant
