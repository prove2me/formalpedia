-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_lemma_35
-- name    : SharedVehicleApprox.Pricing.Supplement.lemma_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:32:45.949243+00:00
-- url     : https://prove2.me/theorems/2b7d2c77-2817-4e22-ab6f-975ad7b94315
-- title:
--   Lemma 35, p. 41 — a Chernoff tail bound for Poisson random variables
-- statement:
--   Let $X$ be a Poisson random variable with mean $\lambda>0$ and let $0\le x\le\lambda$. Then
--
--   $$\mathbb P[X>\lambda+x]\le\exp\Bigl(-\frac{x^2}{2\lambda}\Bigl(1-\frac{x}{\lambda}\Bigr)\Bigr).$$
--
--   In the proof of Lemma 17 this bounds the probability that too many units are in transit at once.
--
--   **Formalization Note** The law is Mathlib's Poisson measure on $\mathbb N$, and the event is the strict one.
--
--   Differences from the source:
--   - encoding: X ∼ Poisson(λ) → Mathlib’s poissonMeasure λ with 0 < λ; reason: the bound divides by λ, so λ = 0 (which forces x = 0) is the case in which the printed formula is undefined
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 41 (PDF 42), App. E, Lemma 35

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Lemma 35, p. 41: for `X ∼ Poisson(lam)` with `lam > 0` and `0 ≤ x ≤ lam`,
`P[X > lam + x] ≤ exp (−(x² / (2 lam)) (1 − x / lam))`. -/
theorem lemma_35 (lam : NNReal) (hlam : 0 < lam) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ (lam : ℝ)) :
    (ProbabilityTheory.poissonMeasure lam).real {k : ℕ | (lam : ℝ) + x < (k : ℝ)} ≤
      Real.exp (-(x ^ 2 / (2 * (lam : ℝ))) * (1 - x / (lam : ℝ))) := by sorry

end SharedVehicleApprox.Pricing.Supplement
