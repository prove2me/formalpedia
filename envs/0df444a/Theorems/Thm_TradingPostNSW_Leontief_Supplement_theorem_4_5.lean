-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_4_5
-- name    : TradingPostNSW.Leontief.Supplement.theorem_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:35:51.505532+00:00
-- url     : https://prove2.me/theorems/9ef6a4c2-33d3-43e1-8c81-70d14e36d734
-- title:
--   Theorem 4.5, p. 15 — TP(∆) with Leontief valuations has a pure Nash equilibrium for every ∆ > 0
-- statement:
--   Consider a Leontief instance ($v_{i,j}\ge0$, $B_i\ge1$, every agent demands some good) with perfect competition, and the Trading Post game $TP(\Delta)$ with entrance fee $\Delta$: a bid below $\Delta$ is ineffective, and agent $i$ receives $\bar b_{i,j}/\sum_k\bar b_{k,j}$ of good $j$ for its effective bid $\bar b_{i,j}>0$. Then for **every** $\Delta>0$, $TP(\Delta)$ has a pure Nash equilibrium.
--
--   This is the existence result behind the goal Theorem 4.9: the fee restores the equilibria that Trading Post without fee can lack (Example 4.4).
--
--   **Formalization Note** The proof's restricted game forces bids of at least $\Delta$ on every demanded good, which is possible only when $|D_i|\Delta\le B_i$; for $\Delta>\max_i B_i$ every profile is an equilibrium. The statement keeps every $\Delta>0$.
--
--   Differences from the source:
--   - encoding: Leontief utilities need demanded goods → the base standing assumption, every agent demands a good; reason: the published base convention
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 15, Theorem 4.5; proof pp. 21–22 (Appendix B)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_4_5 {n m : ℕ} (I : Instance n m) (hI : Standing I)
    (hpc : PerfectCompetition I) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ b : Fin n → Fin m → ℝ, IsPNE I Δ b := by sorry

end TradingPostNSW.Leontief.Supplement
