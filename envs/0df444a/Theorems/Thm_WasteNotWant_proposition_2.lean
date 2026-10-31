-- Prove2me | Theorems.Thm_WasteNotWant_proposition_2
-- name    : WasteNotWant.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:44.444048+00:00
-- url     : https://prove2.me/theorems/04b7b341-849f-4da1-8a7a-73410a9f736a
-- title:
--   Proposition 2 — quick response cuts deadstock finished goods but raises deadstock fabric and total deadstock
-- statement:
--   Let $\mu$ be a market law on $[a,b]$. Optimal decisions exist in the benchmark model and, for every $\delta>0$, in the quick response model. Write $\Theta_l$ for expected deadstock finished goods and $\Theta_m$ for expected deadstock fabric, with superscript $Q$ or $B$ for the model.
--
--   For every $\delta>0$, every optimal $(x^Q,q^Q)$ at $\delta$ and every optimal $(x^B,q^B)$, evaluating each quantity at its model's optimal decisions:
--
--   1. $\Theta^Q_l\le\Theta^B_l$;
--   2. $\Theta^Q_m\ge\Theta^B_m$;
--   3. $\Theta^Q_m+\Theta^Q_l\ge\Theta^B_m+\Theta^B_l$.
--
--   Moreover, for $0<\delta_1\le\delta_2$, with $\Theta^Q(\delta_i)$ evaluated at any optimal pair at $\delta_i$ and with the stage-2 rule at $\delta_i$:
--
--   4. $\Theta^Q_l(\delta_1)\le\Theta^Q_l(\delta_2)$, $\;\Theta^Q_m(\delta_1)\ge\Theta^Q_m(\delta_2)$, and $(\Theta^Q_m+\Theta^Q_l)(\delta_1)\ge(\Theta^Q_m+\Theta^Q_l)(\delta_2)$,
--
--   and all three inequalities are strict when $\delta_1<\delta_2$ and $\delta_1<\bar\delta^Q$.
--
--   So quick response reduces leftover finished goods, but the increase in leftover fabric dominates, total deadstock rises, and all three effects grow as quick response gets cheaper. This is the paper's first main finding.
--
--   Differences from the source:
--   - reading: market size with cdf F on support [a, b] → law μ with cdf F = cdf μ: probability measure carried by [a, b], positive on every open subinterval, no atoms, 0 ≤ a < b; reason: the fractile equations with levels in (0, 1) presuppose a continuous, strictly increasing F; Y is a number of consumers, and a = b would be an atom
--   - reading: p_f > c + c_m → p_f > c + c_m together with p_f < 1, c_m > 0, c ≥ 0; reason: valuations are uniform on [0, 1] and the paper divides by 1 − p_f; c and c_m are unit costs; at c_m = 0 the optimal fabric level is not unique
--   - reading: maximize subject to q ≤ x → maximize over the set 0 ≤ q ≤ x; reason: the proof on p.44 states the constraints q ≤ x, q ≥ 0, x ≥ 0
--   - reading: as δ decreases, the quantities increase or decrease → weak monotonicity over all 0 < δ₁ ≤ δ₂; reason: the quantities are constant on [δ̄^Q, ∞) by Lemma 1(ii)
--   - generalization: no strictness claim in the statement → additionally strict for δ₁ < δ₂ with δ₁ < δ̄^Q; reason: these are the derivative signs of the proof on p.45; the weak claim is the conjunct above
--   - generalization: no existence claim in the statement → existence of optimal decisions in both models, for every δ > 0; reason: the statement is about optimal decisions; asserting existence rules out a vacuous reading
--   - encoding: x^Q, q^Q, x^B, q^B written as functions of δ → statement for every optimal pair; reason: the optimizer is unique under the readings, by Lemma 1 and the benchmark characterization
--   - encoding: Θ^B_m = 0 → Θ^B_m := (x − q)^+ at the decision (x, q); reason: equals 0 at the benchmark optimum, where x^B = q^B
--   - encoding: Θ^Q_m written without its arguments → Θ^Q_m evaluated with the stage-2 rule of the δ at which the pair is optimal; reason: this is the expression E[(x^Q − q^Q − q^Q_δ)^+] of p.12 at that δ
-- source:
--   Long–Gui, Waste Not Want Not?, SSRN 4013877 (2023-08-10 copy), Proposition 2, p.13

import Mathlib
import Definitions.Def_WasteNotWant_Model

open MeasureTheory

namespace WasteNotWant

/-- **Proposition 2: quick response cuts deadstock finished goods but raises deadstock fabric and
total deadstock.**
Long–Gui, *Waste Not Want Not?*, SSRN 4013877 (2023-08-10 copy), Proposition 2, p.13: (i)
`Θ^Q_l ≤ Θ^B_l`, (ii) `Θ^Q_m ≥ Θ^B_m`, (iii) `Θ^Q_m + Θ^Q_l ≥ Θ^B_m + Θ^B_l`, and (iv) as `δ`
decreases, `Θ^Q_l` decreases, `Θ^Q_m` increases and `Θ^Q_m + Θ^Q_l` increases.

The theorem has four conjuncts: optimal benchmark decisions exist; optimal quick-response decisions
exist at every `δ > 0`; (i)–(iii) hold at every `δ > 0` for every pair of optimal decisions; (iv)
holds for every `0 < δ₁ ≤ δ₂` and every optimal pairs at `δ₁` and `δ₂`.

**Formalization Note.** Each deadstock is evaluated at the optimal decisions of its model, and
`Θ^Q_m` also at the `δ` at which those decisions are optimal, since it depends on `δ` through the
stage-2 rule. Over all `δ > 0` the monotonicity in (iv) is weak, since the quantities are constant
on `[δ̄^Q, ∞)` by Lemma 1(ii). The inner implication adds strictness for `δ₁ < δ₂` with `δ₁ < δ̄^Q`,
which is the sign of the derivatives in the proof on p.45. -/
theorem proposition_2 (P : Params) {μ : Measure ℝ} {a b : ℝ} (hμ : IsMarketLaw μ a b) :
    (∃ x q : ℝ, IsBenchmarkOptimal P μ x q) ∧
    (∀ δ : ℝ, 0 < δ → ∃ x q : ℝ, IsQROptimal P μ δ x q) ∧
    (∀ δ xQ qQ xB qB : ℝ, 0 < δ → IsQROptimal P μ δ xQ qQ → IsBenchmarkOptimal P μ xB qB →
      deadstockGoods P μ qQ ≤ deadstockGoods P μ qB ∧
      deadstockFabricBenchmark xB qB ≤ deadstockFabricQR P μ δ xQ qQ ∧
      deadstockFabricBenchmark xB qB + deadstockGoods P μ qB ≤
        deadstockFabricQR P μ δ xQ qQ + deadstockGoods P μ qQ) ∧
    (∀ δ₁ δ₂ x₁ q₁ x₂ q₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
      IsQROptimal P μ δ₁ x₁ q₁ → IsQROptimal P μ δ₂ x₂ q₂ →
      deadstockGoods P μ q₁ ≤ deadstockGoods P μ q₂ ∧
      deadstockFabricQR P μ δ₂ x₂ q₂ ≤ deadstockFabricQR P μ δ₁ x₁ q₁ ∧
      deadstockFabricQR P μ δ₂ x₂ q₂ + deadstockGoods P μ q₂ ≤
        deadstockFabricQR P μ δ₁ x₁ q₁ + deadstockGoods P μ q₁ ∧
      (δ₁ < δ₂ → δ₁ < threshold P →
        deadstockGoods P μ q₁ < deadstockGoods P μ q₂ ∧
        deadstockFabricQR P μ δ₂ x₂ q₂ < deadstockFabricQR P μ δ₁ x₁ q₁ ∧
        deadstockFabricQR P μ δ₂ x₂ q₂ + deadstockGoods P μ q₂ <
          deadstockFabricQR P μ δ₁ x₁ q₁ + deadstockGoods P μ q₁)) := by sorry

end WasteNotWant
