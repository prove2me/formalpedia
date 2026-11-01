-- Prove2me | Theorems.Thm_TaylorInv_eq_A18
-- name    : TaylorInv.eq_A18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:15.349935+00:00
-- url     : https://prove2.me/theorems/dda00977-220b-4a19-aa57-141d736372b9
-- title:
--   (A18) — Hoeffding bound for $\sum_j\sum_p\beta_{jp}x_{jp}$
-- statement:
--   Under the standing assumptions, for every $\delta\ge0$,
--   $$
--   \mathbb P\Big(\Big|\sum_{j=1}^J\sum_{p=1}^P\beta_{jp}(x_{jp}-\mathbb Ex_{jp})\Big|\ge\delta\Big)\le2\exp\Big(-\frac{\delta^2}{2\bar M^2\|\beta\|_2^2}\Big)\le2\exp\Big(-\frac{\delta^2}{2JP\bar M^2\bar B^2}\Big),
--   $$
--   where $\|\beta\|_2^2=\sum_j\sum_p\beta_{jp}^2$.
--
--   This is Hoeffding's inequality for the summands $\beta_{jp}x_{jp}$, which lie in intervals of half-width $|\beta_{jp}|\bar M$; it drives every probability bound of the proof.
--
--   Differences from the source:
--   - encoding: noise $\epsilon_j$ independent of $x_j$; $C_j$ and the retailer costs are conditional expectations $\mathbb E_{\epsilon_j}[\cdot\mid x_j]$ → the noise enters through its density $f_j$ on $[lo_j,hi_j]$, the costs are integrals against $f_j$; the features are random variables on $(\Omega,\mu)$; reason: with $\epsilon_j$ independent of $x_j$ the conditional expectation is this integral; same instances
--   - encoding: $\mathbb E x_{jp}=0$ without loss of generality (p.OA6) and the sum $\sum_j\sum_p\beta_{jp}x_{jp}$ → the centred sum $\sum_j\sum_p\beta_{jp}(x_{jp}-\mathbb E x_{jp})$; reason: the paper's own recentring of the features (p.OA6); the statement is the same after it
--   - encoding: $\mathbb P(\cdot)$ of the event → the (outer) measure of the event, bounded by `ENNReal.ofReal`; reason: same value on measurable events
-- source:
--   Huang, Shang, Yang & Zhou, Taylor Approximation of Inventory Policies for One-Warehouse, Multi-Retailer Systems with Demand Feature Information, SSRN 3993516 (Jan 29 2023), https://ssrn.com/abstract=3993516, (A18), p.OA7

import Mathlib
import Definitions.Def_TaylorInv_Policies

open MeasureTheory ProbabilityTheory

namespace TaylorInv

/-- (A18) (Huang, Shang, Yang & Zhou, SSRN 3993516 (Jan 29 2023), p.OA7): for every `δ ≥ 0`,
`ℙ(|∑_j ∑_p β_jp x_jp| ≥ δ) ≤ 2 exp(−δ²/(2 M̄² ‖β‖₂²)) ≤ 2 exp(−δ²/(2 J P M̄² B̄²))`, with
`‖β‖₂² = ∑_j ∑_p β_jp²`.

**Formalization Note** The paper assumes `𝔼 x_jp = 0` without loss of generality (p.OA6); the sum
here is centred, `∑_j ∑_p β_jp (x_jp − 𝔼 x_jp)` (`centredSum`). The probability is the (outer)
measure of the event. -/
theorem eq_A18 {J P : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : Model J P Ω)
    {Dbar ϵbar Bbar Mbar σbar : ℝ} (hA : M.Assumptions Dbar ϵbar Bbar Mbar σbar μ)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    μ {ω | δ ≤ |M.centredSum μ ω|}
        ≤ ENNReal.ofReal (2 * Real.exp (-δ ^ 2 / (2 * Mbar ^ 2 * ∑ j, ∑ p, M.β j p ^ 2))) ∧
      2 * Real.exp (-δ ^ 2 / (2 * Mbar ^ 2 * ∑ j, ∑ p, M.β j p ^ 2))
        ≤ 2 * Real.exp (-δ ^ 2 / (2 * J * P * Mbar ^ 2 * Bbar ^ 2)) := by sorry

end TaylorInv
