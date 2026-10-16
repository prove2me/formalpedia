-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_proposition_6
-- name    : TokenFinance.MoralHazard.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:32.751718+00:00
-- url     : https://prove2.me/theorems/8e54b51e-4f43-4610-819b-e7f9ff3604a0
-- title:
--   Proposition 6, pp. 29–30 — debt with moral hazard: effort always if λ ≤ δ; if λ > δ, effort iff (24)
-- statement:
--   Assume the standing assumptions of §IV ($0<c<\theta_l<\theta_h$, $C_0>0$, $\mathrm{NPV}_l\le0<\mathrm{NPV}_h$, $C_e<\mathrm{NPV}_h$). Let $D\ge0$ be the break-even face value at $\theta_h$, $\mathbb E_{\theta_h}[\min\{\pi^m,D\}]=C_0$, and set $\delta=2\sqrt D/(\theta_h-c)$ (23), $\lambda=(\theta_l-c)/(\theta_h-c)$ (19). Write IC for the debt incentive constraint (22),
--   $$\mathbb E_{\theta_h}[\max\{\pi^m-D,0\}]-C_e\ \ge\ \mathbb E_{\theta_l}[\max\{\pi^m-D,0\}].$$
--
--   1. If $\lambda\le\delta$, IC holds and the project can be financed by debt.
--   2. If $\lambda>\delta$, IC holds if and only if
--   $$\mathrm{NPV}_h-C_e\ \ge\ \frac{(\lambda-\delta)^2}{(1-\delta)^2}\times\frac{\lambda+2\delta}{1+2\delta}\times\frac{\theta_h}{\theta_l}\times\mathrm{NPV}_h. \tag{24}$$
--
--   **Formalization Note** The page's "exerts effort only when (24) is satisfied" is the result of integrating and rearranging (22), so the equivalence is posed. $\lambda$ is written `lam`.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 29–30 (PDF 30–31), Proposition 6, (24); p. 43 (PDF 44), (49)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable

namespace TokenFinance.MoralHazard

/-- Proposition 6 (pp. 29–30): under the break-even debt contract `D` at `θh`, with
`δ = 2√D/(θh − c)` (23) and `λ = (θl − c)/(θh − c)` (19): if `λ ≤ δ` the entrepreneur always
exerts effort and the project can be financed by debt; if `λ > δ` she exerts effort exactly when
(24) holds. -/
theorem proposition_6 (c C0 Ce θl θh D δ lam : ℝ) (hA : MHAssumptions c C0 Ce θl θh)
    (hD : 0 ≤ D) (hBE : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0)
    (hδ : δ = 2 * Real.sqrt D / (θh - c)) (hlam : lam = (θl - c) / (θh - c)) :
    (lam ≤ δ →
      TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D) - Ce ≥ TokenFinance.Debt.expect θl (TokenFinance.Debt.debtEnt c D) ∧
        DebtFinanceable c C0 Ce θl θh) ∧
    (δ < lam →
      (TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D) - Ce ≥ TokenFinance.Debt.expect θl (TokenFinance.Debt.debtEnt c D) ↔
        TokenFinance.Debt.npv c C0 θh - Ce ≥
          (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) * (θh / θl) *
            TokenFinance.Debt.npv c C0 θh)) := by sorry

end TokenFinance.MoralHazard
