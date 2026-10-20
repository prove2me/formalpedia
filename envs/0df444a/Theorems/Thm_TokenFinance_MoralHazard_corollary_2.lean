-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_corollary_2
-- name    : TokenFinance.MoralHazard.corollary_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:27.663606+00:00
-- url     : https://prove2.me/theorems/f33a5a3c-c3cd-4ac2-a1b1-534aad6aa580
-- title:
--   Corollary 2, p. 30 — every project financeable by equity is financeable by debt, and not conversely
-- statement:
--   Under the standing assumptions of §IV (see the definition of financeability):
--
--   1. every project that can be financed by equity under moral hazard can also be financed by debt;
--   2. the converse fails: there are parameters $(c,C_0,C_e,\theta_l,\theta_h)$ satisfying the standing assumptions for which the project can be financed by debt but not by equity.
--
--   **Formalization Note** "The converse is not true" is posed as the existence of a separating instance; Appendix B ($\theta_h\in\{57,60\}$) provides one.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 30 (PDF 31), Corollary 2

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable

namespace TokenFinance.MoralHazard

/-- Corollary 2 (p. 30): every project that can be financed by equity can be financed by debt;
the converse is not true. -/
theorem corollary_2 :
    (∀ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh →
      EquityFinanceable c C0 Ce θl θh → DebtFinanceable c C0 Ce θl θh) ∧
    (∃ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh ∧
      DebtFinanceable c C0 Ce θl θh ∧ ¬ EquityFinanceable c C0 Ce θl θh) := by sorry

end TokenFinance.MoralHazard
