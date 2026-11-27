-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_4_1
-- name    : TradingPostNSW.Leontief.Supplement.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:34:02.054696+00:00
-- url     : https://prove2.me/theorems/06354002-fa3d-451b-ac51-48f4af0a5f11
-- title:
--   Theorem 4.1, p. 12 — Trading Post with linear valuations has price of anarchy at most 2
-- statement:
--   Let $n$ agents with linear valuations $v_{i,j}\ge0$ and budgets $B_i\ge1$ play the **Trading Post** game: agent $i$ splits its budget into bids $b_i\in[0,B_i]^m$ with $\sum_j b_{i,j}=B_i$, and receives $x_{i,j}=b_{i,j}/\sum_k b_{k,j}$ of good $j$ when $b_{i,j}>0$. Assume perfect competition: every good is valued positively by two distinct agents. Then every pure Nash equilibrium $b$ satisfies, for every feasible allocation $y$,
--   $$NSW(y)\ \le\ 2\,NSW\big(x(b)\big).$$
--
--   Trading Post thus matches the Fisher Market Mechanism's guarantee for substitutes (Theorem 3.3).
--
--   Differences from the source:
--   - encoding: price of anarchy at most c (a maximum of ratios NSW(x*)/NSW(x)) → NSW(y) ≤ c·NSW(x) for every feasible y and every equilibrium outcome x; reason: the multiplicative form avoids dividing by NSW(x); it is the ratio bound with a/0 = ∞
--   - encoding: the Trading Post allocation x_{i,j} = b_{i,j}/Σ_k b_{k,j} if b_{i,j} > 0, else 0 (p. 12) → the base allocation of TP(0), whose effective bids equal the bids for every b ≥ 0; reason: the same allocation on every strategy profile
--   - reading: Nash equilibrium → pure Nash equilibrium; reason: §2 (p. 6) defines the price of anarchy over the set E of pure Nash equilibria
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 12, Theorem 4.1; proof pp. 12–13

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_4_1 {n m : ℕ} (I : Instance n m) (hI : LinStanding I)
    (hpc : PerfectCompetition I) (b : Fin n → Fin m → ℝ) (hb : IsPNEU I (linU I) 0 b)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    NSWU I (linU I) y ≤ 2 * NSWU I (linU I) (tpAlloc 0 b) := by sorry

end TradingPostNSW.Leontief.Supplement
