-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_lemma_4
-- name    : TokenFinance.MoralHazard.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:48.033419+00:00
-- url     : https://prove2.me/theorems/58bce143-32e5-4bdc-aafe-61e502912ee1
-- title:
--   Lemma 4, p. 30 — for 0 < δ < λ < 1, λ³ > (λ−δ)²/(1−δ)² · (λ+2δ)/(1+2δ)
-- statement:
--   For real numbers $0<\delta<\lambda<1$,
--   $$\lambda^3\ >\ \frac{(\lambda-\delta)^2}{(1-\delta)^2}\times\frac{\lambda+2\delta}{1+2\delta}. \tag{25}$$
--
--   Comparing (24) with (20), it shows that whenever the debt incentive constraint is relevant ($\lambda>\delta$) it is weaker than the equity incentive constraint.
--
--   **Formalization Note** The page states the lemma "for $\delta<\lambda<1$"; its proof (p. 43) assumes $0<\delta<\lambda<1$, and at $\delta=0$ the two sides are equal. The hypothesis $0<\delta$ is therefore added; it holds for every break-even debt contract.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 30 (PDF 31), Lemma 4, (25); p. 43 (PDF 44), proof of Lemma 4

import Mathlib

namespace TokenFinance.MoralHazard

/-- Lemma 4 (p. 30), (25): for `0 < δ < λ < 1`,
`λ³ > (λ − δ)²/(1 − δ)² · (λ + 2δ)/(1 + 2δ)`. -/
theorem lemma_4 (δ lam : ℝ) (hδ : 0 < δ) (hδl : δ < lam) (hl1 : lam < 1) :
    lam ^ 3 > (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) := by sorry

end TokenFinance.MoralHazard
