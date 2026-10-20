-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_appendixB_theta57
-- name    : TokenFinance.MoralHazard.appendixB_theta57
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:34.183979+00:00
-- url     : https://prove2.me/theorems/d16ac8ee-fc93-4848-a964-5152b734ca4f
-- title:
--   Appendix B, pp. 45–47 — with C₀ = 110, c = 10, θl = 50, C_e = 25, θh = 57: financeable by debt only
-- statement:
--   Take $C_0=110$, $c=10$, $\theta_l=50$, $C_e=25$ and $\theta_h=57$. Then
--
--   1. the standing assumptions of §IV hold ($\mathrm{NPV}_l\approx-3.3\le0<25<\mathrm{NPV}_h\approx41.8$);
--   2. the project can be financed by debt;
--   3. the project cannot be financed by the optimal token contract;
--   4. the project cannot be financed by equity.
--
--   This instance separates tokens from debt.
--
--   **Formalization Note** The page rounds to one decimal ($D\approx236.7$, $t\approx5.7$); the statement is the exact claim. Since the break-even pre-sale $t$ is unique, "cannot be financed by tokens" amounts to the failure of (27) at that $t$. The page prints $\mathbb E[\pi^m_h]-C_0=\frac1{12}(\theta_h-c)^3/\theta_h$ without the $-C_0$ on the right; the numbers it reports are NPVs.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 45–47 (PDF 46–48), Appendix B

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable

namespace TokenFinance.MoralHazard

/-- Appendix B (pp. 45–47), `θh = 57`: with `C₀ = 110`, `c = 10`, `θl = 50`, `C_e = 25`, the
standing assumptions hold and the project can be financed by debt only. -/
theorem appendixB_theta57 :
    MHAssumptions 10 110 25 50 57 ∧ DebtFinanceable 10 110 25 50 57 ∧
      ¬ TokenFinanceable 10 110 25 50 57 ∧ ¬ EquityFinanceable 10 110 25 50 57 := by sorry

end TokenFinance.MoralHazard
