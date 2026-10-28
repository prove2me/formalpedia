-- Prove2me | Theorems.Thm_RiskPremiaDMP_Equivalence_artificial_productivity
-- name    : RiskPremiaDMP.Equivalence.artificial_productivity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:16.442989+00:00
-- url     : https://prove2.me/theorems/a1121823-1c55-4c6d-b37b-f4e15cbc69cd
-- title:
--   §3, p. 15 (PDF 16), (26)–(27) — substituting (21) into (12) and (15) gives the productivity process of the artificial economy
-- statement:
--   Consider the economy with risk premia under its standing assumptions. Let $y,\eta$ be continuous real paths and $B^{y,\mathcal Q},B^{\eta,\mathcal P}$ real paths such that $y$ solves the risk-neutral productivity equation (15) driven by $B^{y,\mathcal Q}$ and $\eta$ solves the market-price-of-risk equation (12),
--   $$\eta_t=\eta_0+\int_0^t\kappa_\eta(\bar\eta-\eta_u)\,du+\sigma_\eta\big(B^{\eta,\mathcal P}_t-B^{\eta,\mathcal P}_0\big)\qquad(t\ge0).$$
--   Set $y^{\mathcal Q}_t=y_t+\sigma_y\bar\eta/\kappa_y$ and $\mu^{\mathcal Q}_t=\sigma_y(\bar\eta-\eta_t)/\kappa_y$ (21). Then, for $t\ge0$,
--   $$\begin{aligned}y^{\mathcal Q}_t&=y^{\mathcal Q}_0+\int_0^t\kappa^{\mathcal Q}_y(\mu^{\mathcal Q}_u-y^{\mathcal Q}_u)\,du+\sigma^{\mathcal Q}_y\big(B^{y,\mathcal Q}_t-B^{y,\mathcal Q}_0\big),\qquad(26a)\\ \mu^{\mathcal Q}_t&=\mu^{\mathcal Q}_0-\int_0^t\kappa^{\mathcal Q}_\mu\mu^{\mathcal Q}_u\,du-\sigma^{\mathcal Q}_\mu\big(B^{\eta,\mathcal P}_t-B^{\eta,\mathcal P}_0\big),\qquad(26b)\end{aligned}$$
--   with $\kappa^{\mathcal Q}_y=\kappa_y$, $\sigma^{\mathcal Q}_y=\sigma_y$, $\kappa^{\mathcal Q}_\mu=\kappa_\eta$, $\sigma^{\mathcal Q}_\mu=\sigma_\eta\sigma_y/\kappa_y$ (27). In other words, $(y^{\mathcal Q},\mu^{\mathcal Q})$ follows the productivity process (1) of an economy without risk premia, with these parameters and with the shock $-B^{\eta,\mathcal P}$ driving long-run productivity.
--
--   A positive discount-rate shock is a negative shock to the artificial long-run productivity.
--
--   **Formalization Note** The equations are pathwise integral equations; continuity of $y$ and $\eta$ makes every integral a Riemann integral of a continuous function.
-- source:
--   Mitra, Seo & Xu, High Discounts and Low Fundamental Surplus, FRB Atlanta Working Paper 2021-22 (Sept. 2021), pp. 14–15 (PDF 15–16), §3, (12), (15), (21), (26a)–(26b), (27)

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

namespace RiskPremiaDMP.Equivalence

theorem artificial_productivity (P : RPParams) (hP : P.Standing) (y η BQ Bη : ℝ → ℝ)
    (hy : Continuous y) (hη : Continuous η)
    (h15 : SolvesRiskNeutralY P y η BQ) (h12 : SolvesMPR P η Bη) :
    SolvesProductivity (artificial P) (fun t => toYQ P (y t)) (fun t => toMuQ P (η t))
      BQ (fun t => -Bη t) := by sorry

end RiskPremiaDMP.Equivalence
