-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_proposition_5
-- name    : TokenFinance.MoralHazard.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:32.027868+00:00
-- url     : https://prove2.me/theorems/ab183d96-a9d6-47ae-ac34-65c8025403e5
-- title:
--   Proposition 5, p. 28 — equity financing with moral hazard works iff NPV_h − C_e ≥ λ³ (θh/θl) NPV_h
-- statement:
--   Let $0<c<\theta_l<\theta_h$, $C_0>0$, $\mathrm{NPV}_h>0$, and $\lambda=(\theta_l-c)/(\theta_h-c)$ as in (19). The project can be financed by equity under moral hazard (the break-even equity share (17) satisfies the incentive constraint (18)) if and only if
--   $$\mathrm{NPV}_h-C_e\ \ge\ \lambda^3\times\frac{\theta_h}{\theta_l}\times\mathrm{NPV}_h. \tag{20}$$
--
--   Since the right-hand side is positive, equity cannot finance some projects whose NPV net of the effort cost is positive.
--
--   **Formalization Note** The page says "can be financed by equity when (20)"; (20) is obtained from (18) by substitution and rearrangement, so the equivalence is posed, and both directions are used in Corollaries 2–3. $\lambda$ is written `lam` ($\lambda$ is a Lean keyword) and tied to $\theta_l,\theta_h,c$ by a hypothesis.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 28 (PDF 29), Proposition 5, (20); p. 27 (PDF 28), (17)–(19)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable

namespace TokenFinance.MoralHazard

/-- Proposition 5 (p. 28): equity financing with moral hazard succeeds exactly when
`NPV_h − C_e ≥ λ³ · (θh/θl) · NPV_h` (20), with `λ = (θl − c)/(θh − c)` (19). -/
theorem proposition_5 (c C0 Ce θl θh lam : ℝ) (hc : 0 < c) (hcl : c < θl) (hlh : θl < θh)
    (hC0 : 0 < C0) (hnpv : 0 < TokenFinance.Debt.npv c C0 θh) (hlam : lam = (θl - c) / (θh - c)) :
    EquityFinanceable c C0 Ce θl θh ↔
      TokenFinance.Debt.npv c C0 θh - Ce ≥ lam ^ 3 * (θh / θl) * TokenFinance.Debt.npv c C0 θh := by sorry

end TokenFinance.MoralHazard
