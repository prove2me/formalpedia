-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_own_report_transfers
-- name    : SecondBestTrade.HalfEfficiency.own_report_transfers
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:58.270906+00:00
-- url     : https://prove2.me/theorems/368f48df-444b-4c67-80fd-01a7e1a887a0
-- title:
--   Lemma A.3 — Own-report transfers
-- statement:
--   Let $m=(x,p)$ have a feasible allocation rule and real-valued transfers. Replace each agent's transfer by its expectation over the other agents at that agent's own report. For every agent $a$ and true/report pair $s,r$,
--   $$\widehat U_a(s;r)=U_a(s;r),\qquad \mathbb E\widehat p_a=\mathbb E p_a.$$
--   The transformed mechanism preserves BIC whenever it holds, interim IR whenever it holds, and ex-ante weak budget balance whenever it holds.
--
--   The result permits transfer normalization without changing any interim incentive or participation quantity. Both buyer payments and seller receipts are covered.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: buyer payments and seller receipts have opposite utility signs → one signed-payment carrier with seller transfer equal to minus its receipt; reason: this is a bijective change of payment coordinates; the original mechanism still has nonnegative payments and receipts
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma A.3 — Own-report transfers, printed p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_PaymentTransforms

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma A.3, printed p. 20 (PDF p. 21). -/
theorem own_report_transfers (N : Market) (m : SignedMechanism N) (hx : feasible N m.q) :
    (∀ a t r, U N (ownReport N m) a t r = U N m a t r) ∧
    (∀ a, expect N ((ownReport N m).t a) = expect N (m.t a)) ∧
    (BIC N m → BIC N (ownReport N m)) ∧
    (IR N m → IR N (ownReport N m)) ∧
    (WBB N m → WBB N (ownReport N m)) := by sorry

end SecondBestTrade.HalfEfficiency
