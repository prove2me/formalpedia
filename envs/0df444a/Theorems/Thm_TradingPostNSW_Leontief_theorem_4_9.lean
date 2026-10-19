-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_theorem_4_9
-- name    : TradingPostNSW.Leontief.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:16.142096+00:00
-- url     : https://prove2.me/theorems/17e38c61-f465-400a-8ab7-e804d748295b
-- title:
--   Theorem 4.9, p. 16 — every PNE of TP(∆) with 0 < ∆ < min{ε/m², 1/m} has NSW within a factor 1 + ε of the optimum (Leontief)
-- statement:
--   Let $\epsilon > 0$ and $0 < \Delta < \min\{\epsilon/m^2, 1/m\}$. Consider an instance with $n$ agents with Leontief valuations and arbitrary budgets $B_i \ge 1$ over $m \ge 1$ divisible goods, in which every agent demands some good and perfect competition holds. If $b$ is a pure Nash equilibrium of the Trading Post game with entrance fee $\Delta$, written $\mathcal{TP}(\Delta)$, and $x(b)$ is its induced allocation, then every feasible allocation $y$ satisfies
--   $$\mathrm{NSW}(y) \;\le\; (1+\epsilon)\,\mathrm{NSW}\big(x(b)\big).$$
--   In words, the price of anarchy of $\mathcal{TP}(\Delta)$ with respect to the Nash social welfare is at most $1+\epsilon$, even for arbitrary budgets.
--
--   This is the main result of §4.2: with a small entrance fee the Trading Post mechanism, a simple strategic market, implements the Nash social welfare objective up to an arbitrarily small loss.
--
--   **Formalization Note** The printed fee bound is $0 < \Delta < \min\{\epsilon^2/m, 1/m\}$. The proof applies Theorem 4.7, whose bound is $\min\{\epsilon/m^2, 1/m\}$; for $\epsilon \le 1/m$ one has $\epsilon^2/m \le \epsilon/m^2$, so every fee allowed by the printed bound is allowed by the corrected one (the two coincide only at $\epsilon = 1/m$), and for large $\epsilon$ the printed statement fails (for $m = 20$, $\epsilon = 1$, $\Delta = 0.0499$ there is an equilibrium with welfare ratio about $2.18$). The goal uses Theorem 4.7's bound for every $\epsilon > 0$, which implies the printed statement whenever $\epsilon \le 1/m$. "Price of anarchy of $1+\epsilon$" is read as at most $1+\epsilon$ and rendered multiplicatively against every feasible allocation, with no division and no maximum over the (possibly empty) equilibrium set. Deviations range over the whole strategy set, including bids below $\Delta$.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 16, Theorem 4.9 (with the fee bound of Theorem 4.7, p. 15)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- Theorem 4.9, p. 16 (with Theorem 4.7's fee bound): for `ε > 0` and `0 < Δ < min{ε/m², 1/m}`,
every pure Nash equilibrium of `TP(Δ)` with Leontief valuations has Nash social welfare at least
a `1/(1+ε)` fraction of that of every feasible allocation. -/
theorem theorem_4_9 {n m : ℕ} (I : Instance n m) (ε Δ : ℝ) (b : Fin n → Fin m → ℝ)
    (hI : Standing I) (hPC : PerfectCompetition I) (hε : 0 < ε) (hΔ : 0 < Δ)
    (hΔε : Δ < ε / (m : ℝ) ^ 2) (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    NSW I y ≤ (1 + ε) * NSW I (tpAlloc Δ b) := by sorry

end TradingPostNSW.Leontief
