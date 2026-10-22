-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_eps_me_sum_price_eq_total_budget
-- name    : TradingPostNSW.Leontief.eps_me_sum_price_eq_total_budget
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:22.493581+00:00
-- url     : https://prove2.me/theorems/e7d1fade-4aa3-4048-963c-ebb1ac2ca615
-- title:
--   Proof of Theorem 4.8, p. 22 — at an ε-market equilibrium the prices sum to the total budget
-- statement:
--   Consider a Fisher market with Leontief valuations satisfying the standing assumptions, and an $\epsilon$-market equilibrium $(p, x)$. Then
--   $$\sum_{j=1}^m p_j = \sum_{i=1}^n B_i .$$
--
--   All agents spend all their money and goods with positive prices are sold out, so the total value of the goods equals the total budget. This normalization is what makes $p$ comparable with the optimal Nash social welfare in the proof of Theorem 4.8.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 22, proof of Theorem 4.8

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- Proof of Theorem 4.8, p. 22: at an `ε`-market equilibrium `(p, x)` the prices sum to the
total budget. -/
theorem eps_me_sum_price_eq_total_budget {n m : ℕ} (I : Instance n m) (ε : ℝ)
    (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) (hI : Standing I) (hME : IsEpsME I ε p x) :
    ∑ j, p j = ∑ i, I.B i := by sorry

end TradingPostNSW.Leontief
