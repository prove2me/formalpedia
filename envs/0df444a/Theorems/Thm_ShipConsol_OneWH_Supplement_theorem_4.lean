-- Prove2me | Theorems.Thm_ShipConsol_OneWH_Supplement_theorem_4
-- name    : ShipConsol.OneWH.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:30:59.124801+00:00
-- url     : https://prove2.me/theorems/1a94e768-16ba-44ff-8d98-18e12931d500
-- title:
--   Theorem 4 — reachable all-or-none policy, volume thresholds, and monotonicity
-- statement:
--   Let 1≤d≤3, let arrivals be independent Bernoulli unit orders with probability α∈[0,1], and let fixed and unit variable costs F,v be nonnegative, convex and non-increasing on [1,∞). For every horizon T≥1 there is a Bellman-optimal policy π and integer volume thresholds τ_t(n)∈{1,…,d}, non-decreasing in n for each t, such that every state reachable from empty under π has all-or-none shipment. At each nonempty reachable state s=(z_1,…,z_n),
--
--   $$z_1\le\tau_t(n)\Longrightarrow\text{ship all }n\text{ orders},\qquad z_1>\tau_t(n)\Longrightarrow\text{ship none}.$$
--
--   The unrestricted Bellman benchmark optimizes over every subset and package partition. Shipment of all orders can use several packages; this statement does not impose a one-package policy. Reachability follows the selected optimal policy rather than all hypothetical states.
--
--   Differences from the source:
--   - encoding: sorted unit-order lists and shipment/package decisions → lists of natural slacks and disjoint finite sets of order-index packages; reason: all subsets and all partitions are enumerated; duplicate slacks represent distinct unit orders
--   - reading: states reachable under the optimal policy in footnote 24 → a chosen optimal policy from empty, following positive-probability arrival sequences; reason: unattainable demand at α=0 or 1 does not create a state of the stochastic system; both endpoint probabilities remain in the domain
--   - encoding: time-dependent volume thresholds → thresholds also assigned arbitrary monotone values at volumes not reached in the finite horizon; reason: only the finite reachable portion constrains decisions; extending a finite monotone sequence creates no restriction on source policies
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), pinned PDF sha256 2cc7647135cddd3db3d07ad21c65ac52502947d2dde5f337f3ab9948547f0a03, Theorem 4, p. 22; proof OA9–OA12 (PDF41–44)

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_Variable

namespace ShipConsol.OneWH.Supplement

theorem theorem_4 (F v : ℝ → ℝ) (hF : CostAssumptions F) (hv : CostAssumptions v)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d ∧ d ≤ 3)
    (T : ℕ) (hT : 1 ≤ T) :
    let D := bernoulliData F v d α
    let M := shippingControl D
    ∃ (π : ℕ → List ℕ → Packages) (τ : ℕ → ℕ → ℕ),
      validThresholds d τ ∧
      (∀ t, 1 ≤ t → t ≤ T → Monotone (τ t)) ∧
      (∀ t s, 1 ≤ t → t ≤ T → validSlacks d s → M.BellmanOptimal t s (π t s)) ∧
      (∀ t s, M.Reachable π T [] t s →
        (shipped (π t s) = Finset.range s.length ∨ shipped (π t s) = ∅) ∧
        (s ≠ [] →
          (minSlack s ≤ τ t s.length → shipped (π t s) = Finset.range s.length) ∧
          (τ t s.length < minSlack s → shipped (π t s) = ∅))) := by sorry

end ShipConsol.OneWH.Supplement
