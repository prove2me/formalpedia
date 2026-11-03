-- Prove2me | Theorems.Thm_ReactiveCapacity_supplier_response_medium
-- name    : ReactiveCapacity.supplier_response_medium
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:11.701537+00:00
-- url     : https://prove2.me/theorems/612b5287-9104-47e6-83ac-b69945921236
-- title:
--   Supplier's inventory under medium reactive capacity: $\alpha_g$, $1-\bar Q$, or the interval $[\alpha_g,1-\bar Q]$ (corrected: exact low-price condition)
-- statement:
--   Let $0\le\bar Q<1-\alpha_g$ and let $\sigma$ be a strategy profile that plays optimally in every subgame after the supplier's inventory decision. Consider a contract with $q>0$ and $w>kq^2$ under which, when the supplier holds $\alpha_g$, the retailer strictly prefers the low price in the bad market:
--   $$
--   (q\theta_L-w)(\alpha_g+\bar Q)>(q\theta_H-w)\alpha_b .
--   $$
--   Under the standing assumptions, the set of inventories $I\ge 0$ that maximize the supplier's expected payoff is
--
--   1. $\{\alpha_g\}$ if $w<kq^2/(1-\rho)$;
--   2. $\{1-\bar Q\}$ if $w>kq^2/(1-\rho)$;
--   3. the interval $[\alpha_g,1-\bar Q]$ if $w=kq^2/(1-\rho)$.
--
--   A low wholesale price makes the supplier hold only the risk-free inventory $\alpha_g$; a price above $kq^2/(1-\rho)$ makes it stock for the whole bad-market demand that its reactive capacity cannot cover. This is the supplier's step in the medium range, from which the two columns of Table B arise.
--
--   Differences from the source:
--   - generalization: the contracts $w=kq^2+\varepsilon$ and $w=kq^2/(1-\rho)+\varepsilon$ (and "the same inventory" for prices in between or above) → every $w>kq^2$, including $w=kq^2/(1-\rho)$; reason: the $\varepsilon$ contracts and the paper's "still sets $I=\alpha_g$ / $1-\bar Q$" remarks are instances.
--   - correction: the standing focus "the retailer targets all consumers iff $I>(\theta_H/\theta_L)\alpha_b-\bar Q$" (OA pp.3–5) and the range $(\theta_H/\theta_L)\alpha_b-\alpha_g<\bar Q$ → the exact condition $(q\theta_L-w)(\alpha_g+\bar Q)>(q\theta_H-w)\alpha_b$ on the contract; reason: the threshold rule is not the retailer's best response (counterexample at the step-one milestone), and the case split of (B1)–(B3) rests only on the low price at $I\ge\alpha_g$.
--   - encoding: "the optimal inventory" → the set of maximizers of the supplier's expected payoff against any continuation that is optimal after the inventory decision; reason: backward induction without a tie rule.
-- source:
--   Jiang–Tian, Effects of Reactive Capacity, SSRN 3308215 (version of May 5, 2022), Online Appendix §I.2, case (B3), OA pp.16–17 (PDF 61–62); same conclusions in (B1), OA pp.11–13, and (B2), OA pp.14–16

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game

namespace ReactiveCapacity

/-- The supplier's inventory response under medium reactive capacity. Jiang–Tian, *Effects of
Reactive Capacity*, SSRN 3308215 (version of May 5, 2022), Online Appendix §I.2, cases (B1)–(B3),
OA pp.10–17 (PDF 55–62); the quoted text is (B3), OA pp.16–17.

Let `0 ≤ Q̄ < 1 − α_g`, let `σ` play optimally in every subgame after the inventory decision, and
let the contract `(q, w)` have `q > 0`, `w > kq²` and `(qθ_L − w)(α_g + Q̄) > (qθ_H − w)α_b` (the
retailer strictly prefers the low price in the bad market when the supplier holds `α_g`). The set of
inventories `I ≥ 0` maximizing the supplier's expected payoff is

1. `{α_g}` if `w < kq²/(1 − ρ)`;
2. `{1 − Q̄}` if `w > kq²/(1 − ρ)`;
3. the interval `[α_g, 1 − Q̄]` if `w = kq²/(1 − ρ)`.

**Formalization Note** The paper treats the contracts `w = kq² + ε` and `w = kq²/(1 − ρ) + ε`;
the statement covers every `w > kq²` under the displayed condition, and the case of equality. -/
theorem supplier_response_medium (P : Params) (hP : P.Standing) (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg) (σ : Profile) (hσ : IsPostInventorySPE P Qbar σ) (q w : ℝ) (hq : 0 < q) (hw : P.cost q < w) (hlow : (q * P.θH - w) * P.αb < (q * P.θL - w) * (P.αg + Qbar)) :
    (w < P.cost q / (1 - P.ρ) →
      {I : ℝ | 0 ≤ I ∧ ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w I} = {P.αg}) ∧
    (P.cost q / (1 - P.ρ) < w →
      {I : ℝ | 0 ≤ I ∧ ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w I} = {1 - Qbar}) ∧
    (w = P.cost q / (1 - P.ρ) →
      {I : ℝ | 0 ≤ I ∧ ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w I} = Set.Icc P.αg (1 - Qbar)) := by sorry

end ReactiveCapacity
