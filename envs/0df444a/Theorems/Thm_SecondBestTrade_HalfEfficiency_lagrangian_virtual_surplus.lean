-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_lagrangian_virtual_surplus
-- name    : SecondBestTrade.HalfEfficiency.lagrangian_virtual_surplus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:02.334721+00:00
-- url     : https://prove2.me/theorems/d33a6c4d-ebf5-43fa-9b1a-0f5b6c0e7a65
-- title:
--   Lemma A.9 — Lagrangian at a useful dual
-- statement:
--   Fix a useful dual $z=(\tau,\alpha,\beta)$. Every transfer coefficient in (A.5) vanishes. For every feasible allocation rule $x$ and unrestricted signed transfer rule $p$,
--   $$L(x,p;z)=(1+\tau)\mathbb E_\pi\sum_{e\in E}\bigl(\widetilde v_{i(e),e}(v_i)-\widetilde c_{j(e),e}(c_j)\bigr)x_e(v,c).$$
--   This removes payments from the useful-dual objective while retaining the full allocation expression, not just its maximum.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: buyer payments and seller receipts have opposite utility signs → one signed-payment carrier with seller transfer equal to minus its receipt; reason: this is a bijective change of payment coordinates; the original mechanism still has nonnegative payments and receipts
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma A.9 — Lagrangian at a useful dual, printed p. 25 (PDF p. 26)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Lagrangian

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma A.9, printed p. 25 (PDF p. 26). -/
theorem lagrangian_virtual_surplus (N : Market) (z : Dual N) (hz : useful N z) :
    coefficientsVanish N z ∧
    ∀ m : SignedMechanism N, feasible N m.q →
      lagrangian N z m = (1 + (z.tau : ℝ)) *
        expect N (fun v => ∑ e, virtualGain N z v e * m.q v e) := by sorry

end SecondBestTrade.HalfEfficiency
