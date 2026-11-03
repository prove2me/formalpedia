-- Prove2me | Theorems.Thm_ReactiveCapacity_supplier_response_high
-- name    : ReactiveCapacity.supplier_response_high
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:19.524312+00:00
-- url     : https://prove2.me/theorems/6dc6dbbb-017d-4b7d-bcfc-2164e7d64b41
-- title:
--   Supplier's inventory under high reactive capacity: exactly $[\max(0,1-\bar Q),\alpha_g]$ (corrected: printed $[I+\bar Q,\alpha_g]$)
-- statement:
--   Let $\bar Q\ge 1-\alpha_g$ and let $\sigma$ be a strategy profile that plays optimally in every subgame after the supplier's inventory decision. Consider a contract with $q>0$ and $w>kq^2$ under which the retailer strictly prefers the low price in the bad market when it can obtain the whole market:
--   $$
--   q\theta_L-w>(q\theta_H-w)\alpha_b .
--   $$
--   Under the standing assumptions, the set of inventories $I\ge 0$ that maximize the supplier's expected payoff is exactly
--   $$
--   \bigl[\max\{0,1-\bar Q\},\ \alpha_g\bigr].
--   $$
--
--   Every inventory in this interval is risk free: the supplier never holds more than the good-market order $\alpha_g$, and together with its reactive capacity it covers the whole bad-market demand. This is the supplier's step behind Table C.
--
--   Differences from the source:
--   - correction: the interval $[I+\bar Q,\alpha_g]$ printed on OA pp.18–19 → $[1-\bar Q,\alpha_g]$; reason: a slip, the main text (p.19, fn 6) has $[1-\bar Q,\alpha_g]$.
--   - encoding: $[1-\bar Q,\alpha_g]$ → $[\max\{0,1-\bar Q\},\alpha_g]$; reason: inventories are nonnegative, which matters only for $\bar Q>1$.
--   - generalization: the contract $w=kq^2+\varepsilon$ (and "the same inventory" for higher $w$) → every $w>kq^2$; reason: the $\varepsilon$ contract and the paper's remark are instances.
--   - correction: the standing focus "the retailer targets all consumers iff $I>(\theta_H/\theta_L)\alpha_b-\bar Q$" → the exact condition $q\theta_L-w>(q\theta_H-w)\alpha_b$; reason: the threshold rule is not the retailer's best response (counterexample at the step-one milestone).
--   - encoding: "any inventory in the interval is optimal" → the set of maximizers is exactly the interval, against any continuation optimal after the inventory decision; reason: backward induction without a tie rule; the paper's analysis also excludes inventories outside the interval.
-- source:
--   Jiang–Tian, Effects of Reactive Capacity, SSRN 3308215 (version of May 5, 2022), Online Appendix §I.2, cases (C1)–(C2), OA pp.18–19 (PDF 63–64); interval also p.19, fn 6 (PDF 19)

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game

namespace ReactiveCapacity

/-- The supplier's inventory response under high reactive capacity. Jiang–Tian, *Effects of
Reactive Capacity*, SSRN 3308215 (version of May 5, 2022), Online Appendix §I.2, cases (C1)–(C2),
OA pp.18–19 (PDF 63–64).

Let `Q̄ ≥ 1 − α_g`, let `σ` play optimally in every subgame after the inventory decision, and let
the contract `(q, w)` have `q > 0`, `w > kq²` and `qθ_L − w > (qθ_H − w)α_b` (the retailer strictly
prefers the low price in the bad market when it can obtain the whole market). The set of inventories
`I ≥ 0` maximizing the supplier's expected payoff is exactly `[max(0, 1 − Q̄), α_g]`.

**Formalization Note** The paper treats `w = kq² + ε` (and states that higher `w` gives the same
inventory); the statement covers every `w > kq²` under the displayed condition. The printed interval
`[I + Q̄, α_g]` (OA pp.18–19) is a slip for `[1 − Q̄, α_g]` (p.19, fn 6); `max(0, ·)` covers
`Q̄ > 1`. -/
theorem supplier_response_high (P : Params) (hP : P.Standing) (Qbar : ℝ) (hQ : 1 - P.αg ≤ Qbar) (σ : Profile) (hσ : IsPostInventorySPE P Qbar σ) (q w : ℝ) (hq : 0 < q) (hw : P.cost q < w) (hlow : (q * P.θH - w) * P.αb < q * P.θL - w) :
    {I : ℝ | 0 ≤ I ∧ ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w I} = Set.Icc (max 0 (1 - Qbar)) P.αg := by sorry

end ReactiveCapacity
