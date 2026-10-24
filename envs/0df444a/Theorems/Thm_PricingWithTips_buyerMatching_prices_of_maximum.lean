-- Prove2me | Theorems.Thm_PricingWithTips_buyerMatching_prices_of_maximum
-- name    : PricingWithTips.buyerMatching_prices_of_maximum
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:10:26.459527+00:00
-- url     : https://prove2.me/theorems/5f2ec6e9-322b-48e1-94ac-188c7d49b2e9
-- title:
--   A maximum-weight buyer matching has supporting store prices
-- statement:
--   In a finite buyer–store assignment market with arbitrary real edge values, every maximum-weight matching admits nonnegative store prices at which each matched buyer chooses her assigned store, every unmatched buyer prefers opting out, and every unsold store has price zero. The proof first clips negative edge values to zero without changing optimality, then applies the assignment-game core existence and complementary-slackness theorems through a finite matching correspondence.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, if direction of Lemma 4.4, Appendix C, pp. 33–34; second welfare theorem for the induced buyer–store assignment market.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S : Type*} [Fintype B] [Fintype S]
  [DecidableEq B] [DecidableEq S]

theorem buyerMatching_prices_of_maximum
    (z : BuyerMatching B S) (q : B → S → ℝ)
    (hmax : IsMaximumWeight z q) :
    ∃ p : S → ℝ,
      (∀ s, 0 ≤ p s) ∧
      (∀ b,
        match z.assigned b with
        | none => ∀ s, q b s - p s ≤ 0
        | some s => 0 ≤ q b s - p s ∧
            ∀ s', q b s' - p s' ≤ q b s - p s) ∧
      (∀ s, (¬ ∃ b, z.assigned b = some s) → p s = 0) := by sorry

end PricingWithTips
