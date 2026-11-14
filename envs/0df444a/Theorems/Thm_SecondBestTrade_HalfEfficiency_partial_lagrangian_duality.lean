-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_partial_lagrangian_duality
-- name    : SecondBestTrade.HalfEfficiency.partial_lagrangian_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:55.141856+00:00
-- url     : https://prove2.me/theorems/189d93ee-b64d-4c93-8b01-ba0d0d1dbb27
-- title:
--   Lemma A.8 — Partial Lagrangian duality
-- statement:
--   Let $z=(\tau,\alpha,\beta)\ge0$, let $L$ be (A.5), and maximize it over pointwise feasible allocations with unrestricted signed transfers. Its supremum $L^*(z)$ satisfies all three conclusions:
--   $$L^*(z)\ge\mathrm{OPT}(P)\qquad\text{for every }z.$$
--   It is finite if and only if every buyer-payment and seller-receipt coefficient vanishes; in that case
--   $$L^*(z)=\sum_{v,c}\pi(v,c)\max_{X\in\mathcal F}\sum_{e\in X}\Xi_e(v,c).$$
--   There exists $z^*\ge0$ with $L^*(z^*)=\mathrm{OPT}(P)$.
--
--   This is both weak duality and attained strong duality for the specified partial Lagrangian. The optimization domain is not restricted to BIC, IR or balanced mechanisms after those constraints have been dualized.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: buyer payments and seller receipts have opposite utility signs → one signed-payment carrier with seller transfer equal to minus its receipt; reason: this is a bijective change of payment coordinates; the original mechanism still has nonnegative payments and receipts
--   - encoding: Lagrangian supremum in the reals with positive infinity allowed → EReal supremum, with negative infinity explicitly excluded in the conclusion; reason: the feasible zero allocation and free real transfers make the domain nonempty; no infinite arithmetic is needed
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma A.8 — Partial Lagrangian duality, printed p. 24 (PDF p. 25)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Lagrangian

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma A.8, printed p. 24 (PDF p. 25), all three parts. -/
theorem partial_lagrangian_duality (N : Market) :
    (∀ z : Dual N, (OPT N : EReal) ≤ lagrangianSup N z) ∧
    (∀ z : Dual N, lagrangianSup N z ≠ ⊥ ∧
      (lagrangianSup N z < ⊤ ↔ coefficientsVanish N z) ∧
      (coefficientsVanish N z → lagrangianSup N z = (XiObjective N z : EReal))) ∧
    ∃ z : Dual N, lagrangianSup N z = (OPT N : EReal) := by sorry

end SecondBestTrade.HalfEfficiency
