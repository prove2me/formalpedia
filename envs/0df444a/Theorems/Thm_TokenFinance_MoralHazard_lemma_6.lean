-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_lemma_6
-- name    : TokenFinance.MoralHazard.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:58.430974+00:00
-- url     : https://prove2.me/theorems/36e7e210-3fc9-4916-8489-de658f56ab33
-- title:
--   Lemma 6, p. 33, as proved in (57), p. 44 — the break-even contract terms satisfy 0 < τ < δ² < δ < 1
-- statement:
--   Let $0<c<\theta_h$, $C_0>0$, $\mathrm{NPV}_h>0$. Let $D\ge0$ be the break-even debt face value and $t\in(0,(\theta_h-c)/2)$ the break-even token pre-sale at $\theta_h$, and set $\delta=2\sqrt D/(\theta_h-c)$ and $\tau=2t/(\theta_h-c)$. Then
--   $$0<\tau<\delta^2<\delta<1 .$$
--
--   Hence the range of $\theta_l$ in which the entrepreneur always exerts effort is larger under debt ($\lambda\le\delta$) than under tokens ($\lambda\le\tau$).
--
--   **Formalization Note** The lemma as printed reads "$\tau<\delta<\lambda$". The part $\delta<\lambda$ is not a property of the contract terms: $\lambda$ depends on $\theta_l$, which the terms do not see (footnote 10), and Proposition 6 explicitly treats $\lambda\le\delta$. The proof on p. 44 establishes $\tau<\delta^2<\delta$ ((57)), which is what is posed; $\delta<1$ and $\tau>0$ are part of the definitions (23), (28) ("$\delta\in(0,1)$", "$\tau\in(0,1)$").
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 33 (PDF 34), Lemma 6; pp. 43–44 (PDF 44–45), proof of Lemma 6, (52)–(57)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.MoralHazard

/-- Lemma 6 (p. 33), as proved in Appendix A, (57) (p. 44): the break-even debt and token
contract terms at `θh` satisfy `0 < τ < δ² < δ < 1`, where `δ = 2√D/(θh − c)` and
`τ = 2t/(θh − c)`. (The printed `δ < λ` is not a property of the contract terms.) -/
theorem lemma_6 (c C0 θh D t δ τ : ℝ) (hc : 0 < c) (hcθ : c < θh) (hC0 : 0 < C0)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θh) (hD : 0 ≤ D) (hBE : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0)
    (ht0 : 0 < t) (ht1 : t < (θh - c) / 2) (hT : TokenFinance.Debt.tokenBreakEven c C0 θh t)
    (hδ : δ = 2 * Real.sqrt D / (θh - c)) (hτ : τ = 2 * t / (θh - c)) :
    0 < τ ∧ τ < δ ^ 2 ∧ δ ^ 2 < δ ∧ δ < 1 := by sorry

end TokenFinance.MoralHazard
