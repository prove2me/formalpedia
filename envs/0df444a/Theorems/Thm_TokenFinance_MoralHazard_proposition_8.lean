-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_proposition_8
-- name    : TokenFinance.MoralHazard.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:49.199925+00:00
-- url     : https://prove2.me/theorems/c546d25f-0946-4383-9058-457324526441
-- title:
--   Proposition 8, p. 34 — under moral hazard, equity-financeable ⊊ token-financeable ⊊ debt-financeable
-- statement:
--   Consider an entrepreneur whose effort, chosen after financing and not contractible, raises the demand parameter from $\theta_l$ to $\theta_h$ at private cost $C_e$, under the standing assumptions of §IV ($0<c<\theta_l<\theta_h$, $C_0>0$, $\mathrm{NPV}_l\le0<\mathrm{NPV}_h$, $C_e<\mathrm{NPV}_h$). Then:
--
--   1. every project that can be financed by equity can be financed by the optimal token contract;
--   2. every project that can be financed by the optimal token contract can be financed by debt;
--   3. some project satisfying the standing assumptions can be financed by tokens but not by equity;
--   4. some project satisfying the standing assumptions can be financed by debt but not by tokens.
--
--   In the paper's words: debt is best at mitigating moral hazard, in the sense that it can finance the largest set of profitable projects; the optimal token financing is second best; the moral hazard is most severe under equity financing, which therefore funds the smallest set of projects.
--
--   **Formalization Note** "Largest", "second best" and "smallest" are read as strict set inclusions, following "the converse is not true" in Corollaries 2–3 and on p. 34; strictness is posed as the existence of separating parameter values (Appendix B gives them). Equity ⊆ debt follows from 1 and 2.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 34 (PDF 35), Proposition 8; p. 33 (PDF 34), §IV.D; pp. 45–47 (PDF 46–48), Appendix B

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable

namespace TokenFinance.MoralHazard

/-- Proposition 8 (p. 34): under moral hazard, every project that can be financed by equity can
be financed by the optimal token contract, and every project that can be financed by tokens can
be financed by debt; both inclusions are strict. -/
theorem proposition_8 :
    (∀ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh →
      EquityFinanceable c C0 Ce θl θh → TokenFinanceable c C0 Ce θl θh) ∧
    (∀ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh →
      TokenFinanceable c C0 Ce θl θh → DebtFinanceable c C0 Ce θl θh) ∧
    (∃ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh ∧
      TokenFinanceable c C0 Ce θl θh ∧ ¬ EquityFinanceable c C0 Ce θl θh) ∧
    (∃ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh ∧
      DebtFinanceable c C0 Ce θl θh ∧ ¬ TokenFinanceable c C0 Ce θl θh) := by sorry

end TokenFinance.MoralHazard
