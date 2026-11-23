-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_4_2
-- name    : TradingPostNSW.Leontief.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:34:37.910451+00:00
-- url     : https://prove2.me/theorems/d1a0eb0a-3fb4-4565-8d54-0502e317f9f2
-- title:
--   Theorem 4.2, p. 13 — Trading Post has price of anarchy no better than e^{1/e}
-- statement:
--   For every constant $c<e^{1/e}\approx1.445$ there are an instance with additive valuations $v_{i,j}\ge0$, budgets $B_i\ge1$ and perfect competition, a pure Nash equilibrium $b$ of the Trading Post game (no fee), and a feasible allocation $y$ with
--   $$NSW\big(x(b)\big)>0\qquad\text{and}\qquad c\cdot NSW\big(x(b)\big)\ \le\ NSW(y).$$
--
--   So the upper bound $2$ of Theorem 4.1 cannot be lowered below $e^{1/e}$.
--
--   **Formalization Note** The proof on p. 13 reuses the instance of Theorem 3.6; in that profile an agent that is the only bidder on its own good can halve that bid without losing the good, so the profile is not a Trading Post equilibrium. The statement is the theorem, with the constant $e^{1/e}$ exactly; a witness must be found by the prover.
--
--   Differences from the source:
--   - encoding: the price of anarchy is no better than e^{1/e} → for every c < e^{1/e} an instance and a pure Nash equilibrium whose NSW is at most NSW(y)/c for some feasible y; reason: a supremum over instances is at least e^{1/e} exactly when every smaller c is exceeded
--   - reading: the ratio NSW(x*)/NSW(x) → NSW(x(b)) > 0 is required; reason: excludes reaching the bound through a zero denominator
--   - reading: the Trading Post mechanism → Trading Post with additive valuations and perfect competition; reason: p. 13 calls Theorems 4.1 and 4.2 the bounds 'of Trading Post with additive valuations', and perfect competition is §4's standing condition
--   - encoding: the Trading Post allocation x_{i,j} = b_{i,j}/Σ_k b_{k,j} if b_{i,j} > 0, else 0 (p. 12) → the base allocation of TP(0), whose effective bids equal the bids for every b ≥ 0; reason: the same allocation on every strategy profile
--   - reading: Nash equilibrium → pure Nash equilibrium; reason: §2 (p. 6) defines the price of anarchy over the set E of pure Nash equilibria
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 13, Theorem 4.2 and its proof

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_4_2 (c : ℝ) (hc : c < Real.exp (1 / Real.exp 1)) :
    ∃ (n m : ℕ) (I : Instance n m), LinStanding I ∧ PerfectCompetition I ∧
      ∃ b : Fin n → Fin m → ℝ, IsPNEU I (linU I) 0 b ∧
        0 < NSWU I (linU I) (tpAlloc 0 b) ∧
        ∃ y : Fin n → Fin m → ℝ, Feasible I y ∧
          c * NSWU I (linU I) (tpAlloc 0 b) ≤ NSWU I (linU I) y := by sorry

end TradingPostNSW.Leontief.Supplement
