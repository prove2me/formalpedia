-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_appendixB_theta60
-- name    : TokenFinance.MoralHazard.appendixB_theta60
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:30.550381+00:00
-- url     : https://prove2.me/theorems/a08ed45d-68d0-4c90-81b9-9addda5f1ace
-- title:
--   Appendix B, pp. 45–47 — with C₀ = 110, c = 10, θl = 50, C_e = 25, θh = 60: financeable by debt and tokens, not by equity
-- statement:
--   Take $C_0=110$, $c=10$, $\theta_l=50$, $C_e=25$ and $\theta_h=60$. Then
--
--   1. the standing assumptions of §IV hold ($\mathrm{NPV}_l\approx-3.3\le0<25<\mathrm{NPV}_h\approx63.6$);
--   2. the project can be financed by the optimal token contract;
--   3. the project can be financed by debt;
--   4. the project cannot be financed by equity.
--
--   This instance separates equity from tokens (and from debt).
--
--   **Formalization Note** The page rounds to one decimal ($D\approx217.6$, $t\approx4.7$); the statement is the exact claim, with $D$ and $t$ the roots of the break-even conditions.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 45–47 (PDF 46–48), Appendix B

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable

namespace TokenFinance.MoralHazard

/-- Appendix B (pp. 45–47), `θh = 60`: with `C₀ = 110`, `c = 10`, `θl = 50`, `C_e = 25`, the
standing assumptions hold and the project can be financed by debt and by tokens but not by
equity. -/
theorem appendixB_theta60 :
    MHAssumptions 10 110 25 50 60 ∧ TokenFinanceable 10 110 25 50 60 ∧
      DebtFinanceable 10 110 25 50 60 ∧ ¬ EquityFinanceable 10 110 25 50 60 := by sorry

end TokenFinance.MoralHazard
