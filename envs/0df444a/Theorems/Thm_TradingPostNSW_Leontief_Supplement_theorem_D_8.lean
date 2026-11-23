-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_D_8
-- name    : TradingPostNSW.Leontief.Supplement.theorem_D_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:39:08.675304+00:00
-- url     : https://prove2.me/theorems/ba0fc368-c1de-440f-82a4-ad259f867fbd
-- title:
--   Theorem D.8, p. 28 (corrected: source claim refuted) — a Leontief Trading Post game with fee 2 and budgets 1 has a non-pure mixed equilibrium
-- statement:
--   The printed purity claim for every positive fee is false. Take two agents and two goods, all valuations and budgets one, and entrance fee $\Delta=2$. This instance satisfies the Leontief standing assumptions and perfect competition, yet
--   $$\exists\sigma,\quad \operatorname{IsMixedNE}(I,u,2,\sigma)\ \land\ \neg\operatorname{IsPure}(\sigma).$$
--   No admissible bid can reach the fee, so every allocation and every utility is zero. Any independent mixed profile is an equilibrium, including one agent mixing equally between $(1,0)$ and $(0,1)$. The formal statement asserts the source assumptions as well as the counterexample. This replaces the false claim with its refutation, without assuming a smaller fee range.
--
--   Differences from the source:
--   - correction: all Nash equilibria of TP(Δ) with Leontief utilities are pure for every Δ > 0 → the two-agent, two-good all-one instance with budgets 1 and fee 2 admits a non-pure mixed equilibrium; reason: no bid reaches the fee and every payoff is zero; DISPROOF.md. The refutation preserves every source assumption and does not discard an unexamined intermediate-fee range
--   - encoding: mixed strategies are probability distributions over S_i (p. 25); equations (20)–(23) write expectations as sums → arbitrary Borel probability measures, admissible almost surely, with product-measure expectations; purity means Dirac marginals; reason: includes discrete and atomless strategies; integrability in IsMixedNE requires the displayed expectations to be actual expectations, not Lean totality values
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 28, Theorem D.8; Lemmas D.5–D.7, pp. 27–28

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_D_8 : LeontiefPurityFails := by sorry

end TradingPostNSW.Leontief.Supplement
