-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_common_pool_transfers
-- name    : SecondBestTrade.HalfEfficiency.common_pool_transfers
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:26.257047+00:00
-- url     : https://prove2.me/theorems/15cc0d58-0dd9-4327-b6df-2498b71b3fa5
-- title:
--   Lemma A.5 — Common-pool transfers
-- statement:
--   Let $p_i:T_i\to\mathbb R_+$ and $p_j:T_j\to\mathbb R_+$ be buyer payments and seller receipts depending only on own reports. Suppose their total expectations agree at $N$. There are finite nonnegative transfers satisfying reportwise strong budget balance and
--   $$\mathbb E_{-i}\widetilde p_i(r,v_{-i},c)=p_i(r),\qquad \mathbb E_{-j}\widetilde p_j(v,r,c_{-j})=p_j(r).$$
--   If $N>0$, the witness may be chosen as
--   $$\widetilde p_i(v,c)=p_i(v_i)S(c)/N,\qquad \widetilde p_j(v,c)=p_j(c_j)B(v)/N,$$
--   where $B(v)=\sum_i p_i(v_i)$ and $S(c)=\sum_j p_j(c_j)$. If $N=0$, all original transfers vanish and zero transfers satisfy the same conclusions.
--
--   The common pool converts equality of expected totals into equality at every report profile while preserving every interim transfer.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: buyer payments and seller receipts have opposite utility signs → one signed-payment carrier with seller transfer equal to minus its receipt; reason: this is a bijective change of payment coordinates; the original mechanism still has nonnegative payments and receipts
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma A.5 — Common-pool transfers, printed p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_PaymentTransforms

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma A.5, printed p. 20 (PDF p. 21). -/
theorem common_pool_transfers (N : Market) (p : ∀ a, Ty N a → ℝ)
    (hp : ∀ a t, 0 ≤ p a t)
    (hbalance : poolSize N p = ∑ j : Fin N.ns, ∑ t,
      N.mass (.inr j) t * p (.inr j) t) :
    ∃ q : Agent N → Profile N → ℝ, poolCorrect N p q ∧
      (0 < poolSize N p → q = poolTransfers N p) ∧
      (poolSize N p = 0 → (∀ a t, p a t = 0) ∧ q = fun _ _ => 0) := by sorry

end SecondBestTrade.HalfEfficiency
