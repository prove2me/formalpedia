-- Prove2me | Theorems.Thm_PELiquidity_Primary_fund_size
-- name    : PELiquidity.Primary.fund_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:56.915972+00:00
-- url     : https://prove2.me/theorems/4740bfe1-051c-4711-ace9-091122a97969
-- title:
--   (C.4), p. 48 — H-market clearing gives μ_H K = I_H − A = (pR − f̄_H)A/(R̄_H − (pR − f̄_H))
-- statement:
--   In an equilibrium with $\mu_H\in(0,1)$, suppose only H-funds are raised and their return $\bar R_H$ exceeds the H-LPs' break-even rate. Write $\bar f_H$ for the expected fee of the optimal H-fund contract and $g=pR-\bar f_H$ for its pledgeable income. Then $0<g<\bar R_H$, and H-LPs supply all their capital. Market clearing and (3) give the full equation (C.4):
--   $$\mu_H K=I_H-A=\frac{gA}{\bar R_H-g}.\qquad\text{(C.4)}$$
--   For a fixed fee, the right-hand side is strictly decreasing as the promised return rises above $g$.
--
--   **Formalization Note** The equilibrium predicate supplies the capital-market and optimal-contract conditions; the theorem makes the market-clearing equality explicit.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 48, Appendix C.3, proof of Proposition 2, Case 2, (C.4)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting
import Definitions.Def_PELiquidity_Primary_Market

namespace PELiquidity.Primary

/-- (C.4), Case 2 of Proposition 2: when only H-funds are raised and their
return exceeds H-LPs' break-even return, the H capital supply is `μ_H K`.
Market clearing and (3) give `μ_H K = I_H - A = (pR - f̄_H) A /
(R̄_H - (pR - f̄_H))`. For a fixed fee the contribution falls strictly as
the promised return rises. -/
theorem fund_size (P : Params) (muH : ℝ) (E : Allocation)
    (hmu0 : 0 < muH) (hmu1 : muH < 1) (hE : IsEquilibrium P muH E)
    (hαL : E.αL = 0) (hRH : grossReturn P.lam P.δH < E.RH) :
    let pledge := P.p * P.R - expectedFee P.p P.p E.fH
    0 < pledge ∧ pledge < E.RH ∧
    muH * P.K = E.IH - P.A ∧
    E.IH - P.A = pledge * P.A / (E.RH - pledge) ∧
    StrictAntiOn (fun Rb : ℝ => pledge * P.A / (Rb - pledge))
      (Set.Ioi pledge) := by sorry

end PELiquidity.Primary
