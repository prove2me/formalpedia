-- Prove2me | Theorems.Thm_PELiquidity_Primary_lemma_C_1
-- name    : PELiquidity.Primary.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:53.03732+00:00
-- url     : https://prove2.me/theorems/ef7a5629-77d1-441e-8e89-ed0c5a22ec76
-- title:
--   Lemma C.1, p. 47 — if L-funds are raised, then R̄*_PE,L = 1 + r(λ, δ_L)
-- statement:
--   Fix the model parameters and a capital share $\mu_H\in(0,1)$ of $H$-LPs. In every private equity market equilibrium without a secondary market in which $L$-funds are raised, $\alpha^*_L>0$, the return to $L$-LPs equals their break-even return:
--   $$\bar R^*_{PE,L}=1+r(\lambda,\delta_L).$$
--
--   $L$-LPs therefore earn no rent whenever they are in the market; any return premium in equilibrium accrues to $H$-LPs.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 47, Appendix C.3, Lemma C.1

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting
import Definitions.Def_PELiquidity_Primary_Market

namespace PELiquidity.Primary

/-- Lemma C.1: in an equilibrium without a secondary market, if L-funds are raised
(`α*_L > 0`) then L-LPs earn exactly their break-even return `1 + r(λ, δ_L)`. -/
theorem lemma_C_1 (P : Params) (muH : ℝ) (hmu0 : 0 < muH) (hmu1 : muH < 1) (E : Allocation)
    (hE : IsEquilibrium P muH E) (hαL : 0 < E.αL) :
    E.RL = grossReturn P.lam P.δL := by sorry

end PELiquidity.Primary
