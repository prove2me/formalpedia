-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_lemma_5
-- name    : TokenFinance.MoralHazard.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:50.614101+00:00
-- url     : https://prove2.me/theorems/f342a7d7-4b21-4057-b071-7417ca156ae7
-- title:
--   Lemma 5, p. 32 — for 0 < τ < λ < 1, λ³ > (λ−τ)³/(1−τ)³
-- statement:
--   For real numbers $0<\tau<\lambda<1$,
--   $$\lambda^3\ >\ \frac{(\lambda-\tau)^3}{(1-\tau)^3}. \tag{30}$$
--
--   Comparing (29) with (20), it shows that the token incentive constraint is weaker than the equity incentive constraint.
--
--   **Formalization Note** The page states the lemma "for $\tau<\lambda<1$"; its proof (p. 43) assumes $0<\tau<\lambda<1$, and at $\tau=0$ the two sides are equal. The hypothesis $0<\tau$ is added; it holds for every break-even token contract.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 32 (PDF 33), Lemma 5, (30); p. 43 (PDF 44), proof of Lemma 5

import Mathlib

namespace TokenFinance.MoralHazard

/-- Lemma 5 (p. 32), (30): for `0 < τ < λ < 1`, `λ³ > (λ − τ)³/(1 − τ)³`. -/
theorem lemma_5 (τ lam : ℝ) (hτ : 0 < τ) (hτl : τ < lam) (hl1 : lam < 1) :
    lam ^ 3 > (lam - τ) ^ 3 / (1 - τ) ^ 3 := by sorry

end TokenFinance.MoralHazard
