-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_pne_bid_zero_or_ge_fee
-- name    : TradingPostNSW.Leontief.pne_bid_zero_or_ge_fee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:15.014408+00:00
-- url     : https://prove2.me/theorems/baa2de5c-34a6-473a-ad6c-fbd421d7f46e
-- title:
--   §4.2, p. 14 — at a PNE of TP(∆) every bid is 0 or at least ∆
-- statement:
--   Consider an instance satisfying the standing assumptions and perfect competition, and an entrance fee $0 < \Delta < 1/m$. If $b$ is a pure Nash equilibrium of $\mathcal{TP}(\Delta)$, then for every agent $i$ and good $j$
--   $$b_{i,j} = 0 \quad\text{or}\quad b_{i,j} \ge \Delta.$$
--
--   A bid strictly between $0$ and the entrance fee buys nothing, so at an equilibrium no money is wasted that way. As a consequence nominal and effective bids coincide at every equilibrium.
--
--   **Formalization Note** The page states this for "any Nash equilibrium" without conditions. Without $\Delta < 1/m$ it fails: if $\Delta > B_i$ for every agent, no bid is effective and every profile is an equilibrium. The statement therefore carries the hypotheses of Theorem 4.7 and the perfect competition condition standing in §4.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 14, §4.2

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- §4.2, p. 14: at a pure Nash equilibrium of `TP(Δ)` every bid is either `0` or at least
the entrance fee `Δ`. -/
theorem pne_bid_zero_or_ge_fee {n m : ℕ} (I : Instance n m) (Δ : ℝ) (b : Fin n → Fin m → ℝ)
    (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ) (hΔm : Δ < 1 / (m : ℝ))
    (hb : IsPNE I Δ b) :
    ∀ i j, b i j = 0 ∨ Δ ≤ b i j := by sorry

end TradingPostNSW.Leontief
