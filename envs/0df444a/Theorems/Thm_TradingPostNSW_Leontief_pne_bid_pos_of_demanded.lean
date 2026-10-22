-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_pne_bid_pos_of_demanded
-- name    : TradingPostNSW.Leontief.pne_bid_pos_of_demanded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:11.372118+00:00
-- url     : https://prove2.me/theorems/a7b23a47-c830-4328-898e-b66ce78295af
-- title:
--   Proof of Theorem 4.7, p. 15 — at a PNE of TP(∆) every agent bids positively on every good it demands
-- statement:
--   Consider an instance satisfying the standing assumptions ($m \ge 1$, $v_{i,j} \ge 0$, $B_i \ge 1$, every demand set $D_i$ nonempty) and perfect competition, and an entrance fee $0 < \Delta < 1/m$. If $b$ is a pure Nash equilibrium of the Trading Post game $\mathcal{TP}(\Delta)$, then
--   $$b_{i,j} > 0 \qquad \text{for every agent } i \text{ and every good } j \in D_i.$$
--
--   This is the first step of the proof of Theorem 4.7: a demanded good left without a bid would give the agent zero utility, which the uniform strategy improves on. Together with the other structure lemmas it makes all prices of the equilibrium positive.
--
--   **Formalization Note** The hypotheses $\Delta < 1/m$ and $B_i \ge 1$ are those of Theorem 4.7 and the paper's standing assumption; they make the uniform bid $B_i/m$ effective.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 15, proof of Theorem 4.7

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- Proof of Theorem 4.7, p. 15: at a pure Nash equilibrium of `TP(Δ)` every agent bids a
positive amount on every good it demands. -/
theorem pne_bid_pos_of_demanded {n m : ℕ} (I : Instance n m) (Δ : ℝ) (b : Fin n → Fin m → ℝ)
    (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ) (hΔm : Δ < 1 / (m : ℝ))
    (hb : IsPNE I Δ b) :
    ∀ i, ∀ j ∈ D I i, 0 < b i j := by sorry

end TradingPostNSW.Leontief
