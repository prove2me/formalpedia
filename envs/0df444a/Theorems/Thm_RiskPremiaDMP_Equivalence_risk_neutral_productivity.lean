-- Prove2me | Theorems.Thm_RiskPremiaDMP_Equivalence_risk_neutral_productivity
-- name    : RiskPremiaDMP.Equivalence.risk_neutral_productivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:59.814692+00:00
-- url     : https://prove2.me/theorems/a69567ff-1752-454c-9181-77bd7d7f2d60
-- title:
--   §2.2, p. 11 (PDF 12), (15)–(16) — along paths, physical productivity (9) is the risk-neutral process (15) driven by B^{y,Q}
-- statement:
--   Consider the economy with risk premia under its standing assumptions ($\kappa_y,\sigma_y,\kappa_\eta,\sigma_\eta>0$, $\beta\in(0,1)$). Let $y$, $\eta$ and $B^{y,\mathcal P}$ be real paths on $[0,\infty)$ with $y$ and $\eta$ continuous, and suppose $y$ solves the physical productivity equation (9),
--   $$y_t=y_0-\int_0^t\kappa_y y_u\,du+\sigma_y\big(B^{y,\mathcal P}_t-B^{y,\mathcal P}_0\big)\qquad(t\ge0).$$
--   Define $B^{y,\mathcal Q}_t=\int_0^t\eta_u\,du+B^{y,\mathcal P}_t$ as in (16). Then $y$ solves the risk-neutral productivity equation (15),
--   $$y_t=y_0+\int_0^t\kappa_y\Big(-\frac{\sigma_y}{\kappa_y}\eta_u-y_u\Big)du+\sigma_y\big(B^{y,\mathcal Q}_t-B^{y,\mathcal Q}_0\big)\qquad(t\ge0).$$
--
--   Under the risk-neutral measure, productivity thus behaves as if its long-run level were the time-varying $-\sigma_y\eta_t/\kappa_y$; this is the input to the artificial productivity process (26a).
--
--   **Formalization Note** The statement is pathwise. That $B^{y,\mathcal Q}$ is a Brownian motion under the risk-neutral measure (14) (Girsanov's theorem) is not formalized. The process $\eta$ enters only through (16), so no equation for $\eta$ is assumed.
-- source:
--   Mitra, Seo & Xu, High Discounts and Low Fundamental Surplus, FRB Atlanta Working Paper 2021-22 (Sept. 2021), pp. 9–11 (PDF 10–12), §2.2, (9), (15), (16)

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

namespace RiskPremiaDMP.Equivalence

theorem risk_neutral_productivity (P : RPParams) (hP : P.Standing) (y η BP : ℝ → ℝ)
    (hy : Continuous y) (hη : Continuous η) (h9 : SolvesPhysicalY P y BP) :
    SolvesRiskNeutralY P y η (riskNeutralBM η BP) := by sorry

end RiskPremiaDMP.Equivalence
