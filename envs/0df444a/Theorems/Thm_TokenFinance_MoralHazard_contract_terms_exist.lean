-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_contract_terms_exist
-- name    : TokenFinance.MoralHazard.contract_terms_exist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:27.567358+00:00
-- url     : https://prove2.me/theorems/35b8a944-9403-4871-a647-c38afc67a88b
-- title:
--   Appendix A, proofs of Propositions 2–3, pp. 39–41 — at θh the break-even debt repayment D and token pre-sale t exist and are unique
-- statement:
--   Let $0<c<\theta_h$, $C_0>0$ and $\mathrm{NPV}_h=\mathbb E_{\theta_h}[\pi^m]-C_0>0$. Then
--
--   1. there is exactly one $D\ge0$ with $\mathbb E_{\theta_h}[\min\{\pi^m,D\}]=C_0$ (the debt break-even condition (21));
--   2. there is exactly one $t\in(0,(\theta_h-c)/2)$ with
--   $$\frac{c}{c+t}\,\frac{2}{3\theta_h}\Big(\frac{\theta_h-c}{2}-t\Big)^3=\frac{(\theta_h-c)^3}{12\theta_h}-C_0 .$$
--
--   These are the contract terms that every financeability statement of the mission refers to; they are what makes "can be financed by equity" imply the existence of debt and token contracts.
--
--   **Formalization Note** The statement restates, at $\theta=\theta_h$, the existence and uniqueness parts of the proofs of Propositions 2 and 3 (missions I and II of this series), because draft items cannot import each other.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 39–41 (PDF 40–42), Appendix A, proofs of Propositions 2 and 3

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.MoralHazard

/-- Appendix A, proofs of Propositions 2 and 3 (pp. 39–41), at `θ = θh`: the debt break-even
condition (21) has a unique solution `D ≥ 0`, and the token break-even condition (16)/(26) has a
unique solution `t ∈ (0, (θh − c)/2)`. -/
theorem contract_terms_exist (c C0 θh : ℝ) (hc : 0 < c) (hcθ : c < θh) (hC0 : 0 < C0)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θh) :
    (∃! D : ℝ, 0 ≤ D ∧ TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0) ∧
    (∃! t : ℝ, 0 < t ∧ t < (θh - c) / 2 ∧ TokenFinance.Debt.tokenBreakEven c C0 θh t) := by sorry

end TokenFinance.MoralHazard
