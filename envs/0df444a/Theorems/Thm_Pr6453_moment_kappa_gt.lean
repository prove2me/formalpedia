-- Prove2me | Theorems.Thm_Pr6453_moment_kappa_gt
-- name    : Pr6453.moment_kappa_gt
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T15:48:45.823874+00:00
-- url     : https://prove2.me/theorems/36f216ad-14c6-4d36-afda-aaf01c1951d7
-- title:
--   PR #6453: the rank-moment inequality at $\kappa = 0.003287014$
-- statement:
--   The two rank histograms of the PR #6453 word satisfy the price inequality at the claimed saving $\kappa = 1643507/500000000 = 0.003287014$:
--
--   $$\sum_{r} T_r\, r^{1-\kappa} \;>\; \sum_{r} P_r\, r^{1-\kappa},$$
--
--   where $T_r$ counts the productive target fields of rank $r$ and $P_r$ the paid calls of rank $r$, and $r^{1-\kappa} = \exp((1-\kappa)\log r)$ with a real exponent.
--
--   This is the numerical step on which the exponent of the construction rests. The pricing engine of the source bisects the difference of the two moments in $\kappa$; its root is $0.00328701955375063425072028\ldots$, and any $\kappa$ strictly below that root makes the recursive call tree of the word cheaper than it is productive, which is what a time bound $O(n(\lg n)^{1-\kappa})$ requires. The claimed value sits $5.5537\times 10^{-9}$ below the crossing, so the margin is $1.2756\times 10^{-3}$ against a total moment of $1.858\times 10^{5}$ — a relative margin of $6.87\times 10^{-9}$, and the inequality is a genuinely tight numerical fact rather than a formal one.
--
--   The support of the two histograms is $19$ ranks: $1,\dots,9,16,17,24,25,32,33,56,57,73,145$. At rank $1$ the two sides contribute their counts with opposite signs (a deficit of $41\,660$), at $\tau = 0$ the inequality is reversed, and at $\tau = 1$ the rank-mass surplus is $760$; the crossing of the two moments lies in between, and this node records that the claimed saving is still on the correct side of it.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/p104-third-anchor-clean-mixed-root/RESULT.json (complete_cost.kappa, .tested, .raw_root_interval, .targets, .paid) and pricing.py (margin k = moment T (1-k) - moment P (1-k)). The inequality is the certificate's own crossing test at the claimed saving.

import Definitions.Def_Pr6453_RankMoments

set_option autoImplicit false

namespace Pr6453

theorem moment_kappa_gt :
    moment paid (1 - (kappa : ℝ)) < moment targets (1 - (kappa : ℝ)) := by
  sorry

end Pr6453
