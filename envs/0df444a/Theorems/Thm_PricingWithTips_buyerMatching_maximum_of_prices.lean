-- Prove2me | Theorems.Thm_PricingWithTips_buyerMatching_maximum_of_prices
-- name    : PricingWithTips.buyerMatching_maximum_of_prices
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:24:41.110025+00:00
-- url     : https://prove2.me/theorems/9185958c-8143-4df5-bd2f-d0188fb8634d
-- title:
--   Buyer-optimal prices imply a maximum-weight matching
-- statement:
--   In a finite buyer–store assignment market, suppose store prices are nonnegative, every buyer receives a utility-maximizing choice (or opts out when unmatched), and every unsold store has zero price. Then the induced buyer–store matching maximizes total edge weight among all feasible matchings. The proof sums each buyer’s utility bound and uses the unit-capacity constraint to count each sold store price exactly once.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, proof of Lemma 4.4, Appendix C, pp. 33–34; first welfare theorem for the induced buyer–store assignment market.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S : Type*} [Fintype B] [Fintype S]
  [DecidableEq B] [DecidableEq S]

theorem buyerMatching_maximum_of_prices
    (z : BuyerMatching B S) (q : B → S → ℝ) (p : S → ℝ)
    (hp : ∀ s, 0 ≤ p s)
    (hbuyer : ∀ b,
      match z.assigned b with
      | none => ∀ s, q b s - p s ≤ 0
      | some s =>
          0 ≤ q b s - p s ∧ ∀ s', q b s' - p s' ≤ q b s - p s)
    (hunsold : ∀ s, (¬ ∃ b, z.assigned b = some s) → p s = 0) :
    IsMaximumWeight z q := by sorry

end PricingWithTips
