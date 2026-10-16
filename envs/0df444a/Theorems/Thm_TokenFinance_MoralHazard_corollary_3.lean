-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_corollary_3
-- name    : TokenFinance.MoralHazard.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:36.449984+00:00
-- url     : https://prove2.me/theorems/103f299d-1b6d-469e-bb06-a70b07b476c7
-- title:
--   Corollary 3, p. 33 — every project financeable by equity is financeable by optimal tokens, and not conversely
-- statement:
--   Under the standing assumptions of §IV:
--
--   1. every project that can be financed by equity under moral hazard can also be financed by the optimal token contract;
--   2. the converse fails: there are parameters satisfying the standing assumptions for which the project can be financed by tokens but not by equity.
--
--   **Formalization Note** "The converse is not true" is posed as the existence of a separating instance; Appendix B ($\theta_h=60$) provides one.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 33 (PDF 34), Corollary 3

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable

namespace TokenFinance.MoralHazard

/-- Corollary 3 (p. 33): every project that can be financed by equity can be financed by the
optimal token contract; the converse is not true. -/
theorem corollary_3 :
    (∀ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh →
      EquityFinanceable c C0 Ce θl θh → TokenFinanceable c C0 Ce θl θh) ∧
    (∃ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh ∧
      TokenFinanceable c C0 Ce θl θh ∧ ¬ EquityFinanceable c C0 Ce θl θh) := by sorry

end TokenFinance.MoralHazard
