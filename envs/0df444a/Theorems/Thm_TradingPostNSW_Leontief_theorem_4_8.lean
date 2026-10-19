-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_theorem_4_8
-- name    : TradingPostNSW.Leontief.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:15.254664+00:00
-- url     : https://prove2.me/theorems/80169e4e-b21a-4e31-b835-51c7978caedb
-- title:
--   Theorem 4.8, pp. 16, 22 — NSW at an ε-market equilibrium for Leontief utilities is at least 1/(1+ε) of the optimum
-- statement:
--   Consider a Fisher market with Leontief valuations satisfying the standing assumptions ($m \ge 1$, $v_{i,j} \ge 0$, $B_i \ge 1$, every $D_i$ nonempty), let $\epsilon > 0$, and let $(p, x)$ be an $\epsilon$-market equilibrium. Then for every feasible allocation $y$
--   $$\mathrm{NSW}(y) \;\le\; (1+\epsilon)\,\mathrm{NSW}(x).$$
--   That is, the Nash social welfare at an $\epsilon$-market equilibrium is at least a $1/(1+\epsilon)$ fraction of the optimal Nash social welfare.
--
--   The paper presents this as of independent interest: approximate market equilibria of Leontief Fisher markets are approximately optimal for the Nash social welfare. With Theorem 4.7 it gives the price-of-anarchy bound of Theorem 4.9.
--
--   **Formalization Note** "Optimal Nash social welfare" is rendered as a bound against every feasible allocation, with no division and no supremum. The $\epsilon$-market equilibrium's clause (iii) ranges over all bundles $y \ge 0$ (the proof's reading, p. 22); with the printed $y \in [0,1]^m$ the theorem is false. Perfect competition is not assumed: this is a statement about Fisher markets.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 16, Theorem 4.8 (restated and proved on p. 22)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- Theorem 4.8, pp. 16, 22: the Nash social welfare at an `ε`-market equilibrium for Leontief
utilities is at least a `1/(1+ε)` fraction of the NSW of every feasible allocation. -/
theorem theorem_4_8 {n m : ℕ} (I : Instance n m) (ε : ℝ) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) (hI : Standing I) (hε : 0 < ε) (hME : IsEpsME I ε p x)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    NSW I y ≤ (1 + ε) * NSW I x := by sorry

end TradingPostNSW.Leontief
