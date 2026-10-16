-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_proposition_7
-- name    : TokenFinance.MoralHazard.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:40.724185+00:00
-- url     : https://prove2.me/theorems/d58cb45a-b9c2-4574-90f6-17bdf2d48050
-- title:
--   Proposition 7, p. 32 — optimal tokens with moral hazard: effort always if λ ≤ τ; if λ > τ, effort iff (29)
-- statement:
--   Assume the standing assumptions of §IV. Let $t\in(0,(\theta_h-c)/2)$ solve the token break-even condition (16) at $\theta=\theta_h$, and set $\tau=2t/(\theta_h-c)$ (28), $\lambda=(\theta_l-c)/(\theta_h-c)$ (19). Write IC for the token incentive constraint (27), with the entrepreneur producing the monopoly quantity:
--   $$\mathbb E_{\theta_h}\big[\pi^e_t(x,q^m(x))\big]-C_e\ \ge\ \mathbb E_{\theta_l}\big[\pi^e_t(x,q^m(x))\big].$$
--
--   1. If $\lambda\le\tau$, IC holds and the project can be financed by tokens.
--   2. If $\lambda>\tau$, IC holds if and only if
--   $$\mathrm{NPV}_h-C_e\ \ge\ \frac{(\lambda-\tau)^3}{(1-\tau)^3}\times\frac{\theta_h}{\theta_l}\times\mathrm{NPV}_h. \tag{29}$$
--
--   **Formalization Note** The equivalence is posed because (29) is a rearrangement of (27). $\lambda$ is written `lam`.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 32 (PDF 33), Proposition 7, (29); p. 31 (PDF 32), (26)–(27)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable

namespace TokenFinance.MoralHazard

/-- Proposition 7 (p. 32): under the break-even token contract `t` at `θh`, with
`τ = 2t/(θh − c)` (28) and `λ = (θl − c)/(θh − c)` (19): if `λ ≤ τ` the entrepreneur always
exerts effort and the project can be financed by tokens; if `λ > τ` she exerts effort exactly
when (29) holds. -/
theorem proposition_7 (c C0 Ce θl θh t τ lam : ℝ) (hA : MHAssumptions c C0 Ce θl θh)
    (ht0 : 0 < t) (ht1 : t < (θh - c) / 2) (hBE : TokenFinance.Debt.tokenBreakEven c C0 θh t)
    (hτ : τ = 2 * t / (θh - c)) (hlam : lam = (θl - c) / (θh - c)) :
    (lam ≤ τ →
      TokenFinance.Debt.expect θh (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) - Ce ≥
          TokenFinance.Debt.expect θl (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) ∧
        TokenFinanceable c C0 Ce θl θh) ∧
    (τ < lam →
      (TokenFinance.Debt.expect θh (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) - Ce ≥
          TokenFinance.Debt.expect θl (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) ↔
        TokenFinance.Debt.npv c C0 θh - Ce ≥ (lam - τ) ^ 3 / (1 - τ) ^ 3 * (θh / θl) * TokenFinance.Debt.npv c C0 θh)) := by sorry

end TokenFinance.MoralHazard
