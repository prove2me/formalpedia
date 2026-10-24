-- Prove2me | Theorems.Thm_PricingWithTips_maximumMatching_max_zero
-- name    : PricingWithTips.maximumMatching_max_zero
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:54:57.98953+00:00
-- url     : https://prove2.me/theorems/73e4ea6f-d3ef-4d9b-ab0a-651f97074219
-- title:
--   Maximum matching remains optimal after clipping negative edge weights
-- statement:
--   For any finite buyer–store matching problem with real edge weights, a matching of maximum total weight is also maximum when every negative edge weight is replaced by zero. An optimal matching never uses a negative edge, because removing that edge improves its weight. For any competing matching, delete its negative edges; its weight under the original weights then equals its weight under clipped weights. This reduction allows nonnegative assignment-game duality to be used for arbitrary adjusted buyer values.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, assignment-market argument in Lemma 4.4, Appendix C, pp. 33–34; elementary matching reduction formalized for its converse.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S : Type*} [Fintype B] [Fintype S]
  [DecidableEq B] [DecidableEq S]

theorem maximumMatching_max_zero
    (z : BuyerMatching B S) (q : B → S → ℝ)
    (hmax : IsMaximumWeight z q) :
    IsMaximumWeight z (fun b s => max 0 (q b s)) := by sorry

end PricingWithTips
