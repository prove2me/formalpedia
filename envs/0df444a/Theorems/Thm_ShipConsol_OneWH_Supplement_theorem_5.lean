-- Prove2me | Theorems.Thm_ShipConsol_OneWH_Supplement_theorem_5
-- name    : ShipConsol.OneWH.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:31:51.32329+00:00
-- url     : https://prove2.me/theorems/62ebf595-16a0-4808-ba75-ee0cfe0e6825
-- title:
--   Theorem 5 — finite-T relative gap of H3 to the best volume-threshold one-package policy H2
-- statement:
--   Let $1\le d\le 3$, let at most one unit order arrive in each period, independently with probability $\alpha\in(0,1)$, and let the unit variable cost be proportional to the fixed cost, $v=\gamma F$ with $\gamma\ge0$, where $F$ is nonnegative, convex and non-increasing on $[1,\infty)$. Fix a horizon of $T\ge1$ periods, start from an empty system and force shipment of everything pending in the last period. Let $\widetilde C$ be the expected cost per period of heuristic H3 (ship all pending orders in one package when the smallest slack $z_1$ is at most a constant threshold $\tau\in\{1,\dots,d\}$, otherwise wait), with $\tau$ chosen optimally, and let $C_0$ be the expected cost per period of the best one-package policy whose threshold $\tau(n)\in\{1,\dots,d\}$ may depend on the number $n$ of pending orders (policy H2). Write $\Delta=F(1)-F(2)$, $a_1=2/\alpha+1$ and $a_2=3/(1-\alpha)$. If $C_0>0$, then
--
--   $$\frac{\widetilde C-C_0}{C_0}\le\min\left\{\frac{\gamma\Delta}{a_1\gamma\Delta+(a_1+a_2)v(2)},\ \frac{\frac{1+(1+3\alpha)(3-\alpha)}{1+2\alpha}F(2)}{\frac{1}{\alpha(1-\alpha)}F(2)+\frac1\alpha\Delta}\right\}.$$
--
--   When $\gamma=0$ the first fraction is $0/0$ and has no value; the bound is then the second fraction alone. The theorem says that allowing volume-dependent thresholds gains little over a single constant threshold when deadlines are short.
--
--   Formalization Note: $\widetilde C$ and $C_0$ are actual finite-horizon expected costs (total divided by $T$) computed from the event order of DP (1), not stationary Markov-chain costs. H2 thresholds depend on the volume only, as H2 is defined on p. 24 and as the proof on OA12 uses them; they are not allowed to depend on time.
--
--   Differences from the source:
--   - encoding: average cost per period for T periods → expected total cost from the empty state with forced terminal shipment, divided by T; reason: the event order and terminal condition of DP (1), pp. 10–11
--   - reading: C₀, the optimal no-splitting policy with varying thresholds → infimum over one-package policies with thresholds τ(n)∈{1,…,d} depending on the number of pending orders; reason: H2 is defined on p. 24 by thresholds that vary with the number of pending orders, p. 25 says Theorem 5 compares H2 with H3, and the proof on OA12 uses τ(m)
--   - reading: printed fractions → α∈(0,1), C₀>0, and at γ=0 the undefined first fraction (0/0) is dropped from the minimum; reason: a₁, a₂ and the ratio are undefined at α∈{0,1} or C₀=0; under C₀>0 every other denominator is positive
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), pinned PDF sha256 2cc7647135cddd3db3d07ad21c65ac52502947d2dde5f337f3ab9948547f0a03, Theorem 5, p. 25; proof OA12–OA13 (PDF44–45)

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_Variable

namespace ShipConsol.OneWH.Supplement

theorem theorem_5 (F : ℝ → ℝ) (hF : CostAssumptions F) (γ : ℝ) (hγ : 0 ≤ γ)
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d ∧ d ≤ 3)
    (T : ℕ) (hT : 1 ≤ T) :
    let D := bernoulliData F (fun x => γ * F x) d α
    0 < h2Average D T →
      (h3Average D T - h2Average D T) / h2Average D T ≤ bound5 F α γ := by sorry

end ShipConsol.OneWH.Supplement
