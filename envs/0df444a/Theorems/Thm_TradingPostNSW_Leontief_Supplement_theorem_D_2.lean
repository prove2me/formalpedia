-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_D_2
-- name    : TradingPostNSW.Leontief.Supplement.theorem_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:37:39.941176+00:00
-- url     : https://prove2.me/theorems/13049817-dd70-4cb6-827b-d70bb0f4d894
-- title:
--   Theorem D.2, p. 26 (corrected: source claim refuted) — a perfectly competitive linear Trading Post game has a non-pure mixed equilibrium
-- statement:
--   The printed universal purity claim is false. Let there be three agents, two goods, budgets $B_i=1$ and valuation vectors $(1,0),(1/10,1),(0,1)$. Every agent values a good and every good is valued by two agents. This instance admits a mixed Nash equilibrium of Trading Post without a fee that is not pure:
--   $$\exists\sigma,\quad \operatorname{IsMixedNE}(I,u^{lin},0,\sigma)\ \land\ \neg\operatorname{IsPure}(\sigma).$$
--   The first agent mixes equally between $(1,0)$ and $(9/10,1/10)$; the other two bid $(0,1)$. The first agent always receives all of its valued good. The second has a negative marginal gain from moving money to good 1 and a concave payoff, and the third spends everything on its only valued good. `DISPROOF.md` gives the exact checks. The formal statement also asserts the standing assumptions, perfect competition and nonempty demands of this fixed instance.
--
--   Differences from the source:
--   - correction: all Nash equilibria of linear Trading Post with perfect competition are pure → an explicit three-agent, two-good instance satisfying perfect competition and nonempty demands admits a non-pure mixed equilibrium; reason: the printed claim is false: valuations (1,0), (1/10,1), (0,1), budgets 1; the first agent mixes (1,0)/(9/10,1/10), the others bid (0,1); DISPROOF.md checks all deviations. This refutes the source without imposing all-positive valuations
--   - encoding: mixed strategies are probability distributions over S_i (p. 25); equations (20)–(23) write expectations as sums → arbitrary Borel probability measures, admissible almost surely, with product-measure expectations; purity means Dirac marginals; reason: includes discrete and atomless strategies; integrability in IsMixedNE requires the displayed expectations to be actual expectations, not Lean totality values
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 26, Theorem D.2; Lemma D.1, pp. 25–26; perfect competition recalled p. 25

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_D_2 : LinearPurityFails := by sorry

end TradingPostNSW.Leontief.Supplement
