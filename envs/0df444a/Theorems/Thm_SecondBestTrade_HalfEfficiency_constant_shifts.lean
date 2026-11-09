-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_constant_shifts
-- name    : SecondBestTrade.HalfEfficiency.constant_shifts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:04.33597+00:00
-- url     : https://prove2.me/theorems/6693a595-ad69-4dc3-b6e1-2134159b9372
-- title:
--   Lemma A.4 — Constant shifts
-- statement:
--   Let $m$ be a feasible BIC, interim IR signed mechanism. For each buyer choose a real constant $\gamma_i$ and for each seller a real constant $\delta_j$. Add $\gamma_i$ to the buyer payment and subtract $\delta_j$ from the seller receipt. Every true/report utility changes by
--   $$U'_i(s;r)=U_i(s;r)-\gamma_i,\qquad U'_j(s;r)=U_j(s;r)-\delta_j.$$
--   The mechanism remains BIC. Writing $m_i=\min_s U_i(s;s)$ and $n_j=\min_s U_j(s;s)$, interim IR holds after the change if and only if
--   $$\gamma_i\le m_i\ (\forall i),\qquad \delta_j\le n_j\ (\forall j).$$
--   This characterizes precisely which constant shifts preserve participation, including negative shifts and singleton supports.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: buyer payments and seller receipts have opposite utility signs → one signed-payment carrier with seller transfer equal to minus its receipt; reason: this is a bijective change of payment coordinates; the original mechanism still has nonnegative payments and receipts
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma A.4 — Constant shifts, printed p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_PaymentTransforms

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma A.4, printed p. 20 (PDF p. 21). -/
theorem constant_shifts (N : Market) (m : SignedMechanism N)
    (hx : feasible N m.q) (hbic : BIC N m) (hir : IR N m) (d : Agent N → ℝ) :
    (∀ a t r, U N (shifted N m d) a t r = U N m a t r - d a) ∧
    BIC N (shifted N m d) ∧
    (IR N (shifted N m d) ↔ ∀ a, d a ≤ minUtility N m a) := by sorry

end SecondBestTrade.HalfEfficiency
