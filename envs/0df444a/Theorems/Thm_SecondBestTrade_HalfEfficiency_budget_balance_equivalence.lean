-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_budget_balance_equivalence
-- name    : SecondBestTrade.HalfEfficiency.budget_balance_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:41.720758+00:00
-- url     : https://prove2.me/theorems/e309935b-8779-4609-ae68-91e8891c7eb3
-- title:
--   Proposition A.1 — Budget-balance equivalence
-- statement:
--   Let $\mathcal M$ be the feasible BIC, interim IR mechanisms with nonnegative transfers and reportwise strong budget balance. Let $\mathcal M'$ allow signed transfers and require only ex-ante weak budget balance. For every feasible allocation rule $x$,
--   $$\bigl(\exists p:(x,p)\in\mathcal M'\bigr)\quad\Longleftrightarrow\quad\bigl(\exists p:(x,p)\in\mathcal M\bigr).$$
--   Consequently,
--   $$\mathrm{SB}=\sup_{(x,p)\in\mathcal M}\mathrm{GFT}(x)=\sup_{(x,p)\in\mathcal M'}\mathrm{GFT}(x),$$
--   and both suprema are attained.
--
--   This identifies the allocation content of the original and relaxed mechanism classes, including the existence of optimizing mechanisms on both sides.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: buyer payments and seller receipts have opposite utility signs → one signed-payment carrier with seller transfer equal to minus its receipt; reason: this is a bijective change of payment coordinates; the original mechanism still has nonnegative payments and receipts
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Proposition A.1 — Budget-balance equivalence, printed p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Mechanisms

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Proposition A.1, printed p. 19 (PDF p. 20). -/
theorem budget_balance_equivalence (N : Market) :
    (∀ x : Allocation N, feasible N x →
      ((∃ m : SignedMechanism N, relaxed N m ∧ m.q = x) ↔
        ∃ m : Mechanism N, admissible N m ∧ m.x = x)) ∧
    SB N = relaxedSB N ∧
    (∃ m : Mechanism N, admissible N m ∧ GFT N m.x = SB N) ∧
    (∃ m : SignedMechanism N, relaxed N m ∧ GFT N m.q = relaxedSB N) := by sorry

end SecondBestTrade.HalfEfficiency
