-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_eq_48
-- name    : TokenFinance.MoralHazard.eq_48
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:59.5721+00:00
-- url     : https://prove2.me/theorems/a33b285b-eda6-4bb7-bded-73eb1f7ff259
-- title:
--   (48), Appendix A, proof of Proposition 6, p. 42 — under the break-even debt, NPV_h = (θh−c)³/(12θh)·(1 − 3δ² + 2δ³)
-- statement:
--   Let $0<c<\theta_h$, $C_0>0$, $\mathrm{NPV}_h>0$, and let $D\ge0$ solve the debt break-even condition $\mathbb E_{\theta_h}[\min\{\pi^m,D\}]=C_0$. With $\delta=2\sqrt D/(\theta_h-c)$ as in (23),
--
--   1. the entrepreneur's expected profit under effort is the NPV: $\mathbb E_{\theta_h}[\max\{\pi^m-D,0\}]=\mathrm{NPV}_h$;
--   2. $$\mathrm{NPV}_h=\frac{(\theta_h-c)^3}{12\theta_h}\,(1-3\delta^2+2\delta^3). \tag{48}$$
--
--   This expresses the debt contract through the single number $\delta$ and is the basis of the comparison with token financing (Lemma 6).
--
--   **Formalization Note** $\mathrm{NPV}_h>0$ is the standing assumption of §IV; without it the break-even face value may exceed the maximal profit and (48) fails.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 42 (PDF 43), Appendix A, proof of Proposition 6, (48)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.MoralHazard

/-- (48), Appendix A, proof of Proposition 6 (p. 42): if `D ≥ 0` solves the debt break-even
condition (21) at `θh`, the entrepreneur's expected profit under effort is `NPV_h`, and
`NPV_h = (θh − c)³/(12θh) · (1 − 3δ² + 2δ³)` with `δ = 2√D/(θh − c)` (23). -/
theorem eq_48 (c C0 θh D δ : ℝ) (hc : 0 < c) (hcθ : c < θh) (hC0 : 0 < C0)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θh) (hD : 0 ≤ D) (hBE : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0)
    (hδ : δ = 2 * Real.sqrt D / (θh - c)) :
    TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D) = TokenFinance.Debt.npv c C0 θh ∧
      TokenFinance.Debt.npv c C0 θh = (θh - c) ^ 3 / (12 * θh) * (1 - 3 * δ ^ 2 + 2 * δ ^ 3) := by sorry

end TokenFinance.MoralHazard
