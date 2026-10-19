-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_theorem_4_7
-- name    : TradingPostNSW.Leontief.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:12.590614+00:00
-- url     : https://prove2.me/theorems/b4df0d8f-e1de-4add-aa3f-8d90d8d48ffa
-- title:
--   Theorem 4.7, p. 15 — every PNE of TP(∆) with Leontief valuations corresponds to an ε-market equilibrium
-- statement:
--   Let $\epsilon > 0$ and $0 < \Delta < \min\{\epsilon/m^2, 1/m\}$. Consider an instance with Leontief valuations satisfying the standing assumptions ($m \ge 1$, $v_{i,j} \ge 0$, $B_i \ge 1$, every $D_i$ nonempty) and perfect competition, and a pure Nash equilibrium $b$ of the Trading Post game $\mathcal{TP}(\Delta)$. Set the prices to the total bids,
--   $$p_j = \sum_{i=1}^n b_{i,j},$$
--   and let $x$ be the allocation induced by $b$. Then $(p, x)$ is an $\epsilon$-market equilibrium: every good with a positive price is sold out, every agent spends exactly its budget, and no bundle $y \ge 0$ affordable at prices $p$ gives agent $i$ more than $(1+\epsilon)\,u_i(x_i)$.
--
--   This is the bridge from the strategic game to market equilibrium theory: combined with Theorem 4.8 it bounds the price of anarchy of $\mathcal{TP}(\Delta)$.
--
--   **Formalization Note** "Corresponds to" is made precise as in the proof: the prices and allocation are those constructed from $b$, not chosen freely. Clause (iii) of the $\epsilon$-market equilibrium ranges over all bundles $y \ge 0$ rather than the printed $y \in [0,1]^m$ (a correction needed for Theorem 4.8; Theorem 4.7 remains true under it).
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 15, Theorem 4.7 (proof pp. 15–16)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- Theorem 4.7, p. 15: for `0 < Δ < min{ε/m², 1/m}`, every pure Nash equilibrium `b` of `TP(Δ)`
with Leontief valuations, with prices `p_j = Σ_i b_{i,j}` and its induced allocation, is an
`ε`-market equilibrium. -/
theorem theorem_4_7 {n m : ℕ} (I : Instance n m) (ε Δ : ℝ) (b : Fin n → Fin m → ℝ)
    (hI : Standing I) (hPC : PerfectCompetition I) (hε : 0 < ε) (hΔ : 0 < Δ)
    (hΔε : Δ < ε / (m : ℝ) ^ 2) (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b) :
    IsEpsME I ε (bidPrice b) (tpAlloc Δ b) := by sorry

end TradingPostNSW.Leontief
