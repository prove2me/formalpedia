-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_lemma_7
-- name    : TokenFinance.MoralHazard.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:00.876833+00:00
-- url     : https://prove2.me/theorems/a8ae7ddb-97b9-4f0b-b6b9-2f46c1f2ff36
-- title:
--   Lemma 7, p. 34 — under the break-even contract terms, for δ < λ < 1: λ³ > (λ−τ)³/(1−τ)³ > (λ−δ)²(λ+2δ)/((1−δ)²(1+2δ))
-- statement:
--   Let $0<c<\theta_h$, $C_0>0$, $\mathrm{NPV}_h>0$, let $D\ge0$ and $t\in(0,(\theta_h-c)/2)$ be the break-even debt face value and token pre-sale at $\theta_h$, and set $\delta=2\sqrt D/(\theta_h-c)$, $\tau=2t/(\theta_h-c)$. For every $\lambda$ with $\delta<\lambda<1$,
--   $$\lambda^3\ >\ \frac{(\lambda-\tau)^3}{(1-\tau)^3}\ >\ \frac{(\lambda-\delta)^2}{(1-\delta)^2}\times\frac{\lambda+2\delta}{1+2\delta}. \tag{31}$$
--
--   Together with Propositions 5–7, the debt incentive constraint (24) is the least restrictive, followed by the token constraint (29) and then the equity constraint (20).
--
--   **Formalization Note** The contract-term hypotheses are essential: as a bare inequality for arbitrary $0<\tau<\delta<\lambda<1$ the second inequality is false (e.g. $\delta=0.5$, $\tau=0.49$, $\lambda=0.8$). The proof (p. 45, (60)) uses $\tau<\delta^2$, which holds for the contract terms (Lemma 6). $\lambda$ is a free number in $(\delta,1)$; every such number is $(\theta_l-c)/(\theta_h-c)$ for some $\theta_l\in(c,\theta_h)$.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 34 (PDF 35), Lemma 7, (31); pp. 44–45 (PDF 45–46), proof of Lemma 7, (58)–(60)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.MoralHazard

/-- Lemma 7 (p. 34), (31): for the break-even debt and token contract terms at `θh`, with
`δ = 2√D/(θh − c)`, `τ = 2t/(θh − c)` and any `λ` with `δ < λ < 1`,
`λ³ > (λ − τ)³/(1 − τ)³ > (λ − δ)²/(1 − δ)² · (λ + 2δ)/(1 + 2δ)`. -/
theorem lemma_7 (c C0 θh D t δ τ lam : ℝ) (hc : 0 < c) (hcθ : c < θh) (hC0 : 0 < C0)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θh) (hD : 0 ≤ D) (hBE : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0)
    (ht0 : 0 < t) (ht1 : t < (θh - c) / 2) (hT : TokenFinance.Debt.tokenBreakEven c C0 θh t)
    (hδ : δ = 2 * Real.sqrt D / (θh - c)) (hτ : τ = 2 * t / (θh - c))
    (hδl : δ < lam) (hl1 : lam < 1) :
    lam ^ 3 > (lam - τ) ^ 3 / (1 - τ) ^ 3 ∧
      (lam - τ) ^ 3 / (1 - τ) ^ 3 >
        (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) := by sorry

end TokenFinance.MoralHazard
