-- Prove2me | Theorems.Thm_RegevLWE_PeriodicGauss_final_evaluation
-- name    : RegevLWE.PeriodicGauss.final_evaluation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:37.318781+00:00
-- url     : https://prove2.me/theorems/4bec9923-9ac7-49cc-92ec-e5fe8c551a29
-- title:
--   Proof of Claim 2.2, p. 34:16 — ϵ + 2πϵ∫x²e^{−πx²/(1+ϵ)²}dx = ϵ + ϵ(1+ϵ)³ ≤ 9ϵ
-- statement:
--   For $0 < \epsilon \le 1$,
--   $$\epsilon + 2\pi\epsilon\int_{\mathbb{R}} x^2 e^{-\pi x^2/(1+\epsilon)^2}\,dx = \epsilon + \epsilon(1+\epsilon)^3 \le 9\epsilon.$$
--
--   This is the last step of the proof of Claim 2.2: it evaluates the Gaussian second moment and bounds the result by $9\epsilon$, the constant of the claim.
--
--   **Formalization Note** The integral is a real (Bochner) integral; its integrand is integrable, so it has its true value, and the equality cannot be made true by the convention that a non-integrable integral is $0$ (that would give $\epsilon = \epsilon + \epsilon(1+\epsilon)^3$, false for $\epsilon > 0$).
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:16, proof of Claim 2.2, last display

import Mathlib
import Definitions.Def_RegevLWE_PeriodicGauss_Gaussian

open MeasureTheory

namespace RegevLWE.PeriodicGauss

/-- Proof of Claim 2.2, p. 34:16, last display: for `0 < ϵ ≤ 1`,
`ϵ + 2πϵ ∫_ℝ x² e^{-πx²/(1+ϵ)²} dx = ϵ + ϵ(1+ϵ)³ ≤ 9ϵ`. -/
theorem final_evaluation (ϵ : ℝ) (hϵ : 0 < ϵ) (hϵ1 : ϵ ≤ 1) :
    ϵ + 2 * Real.pi * ϵ * ∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) =
        ϵ + ϵ * (1 + ϵ) ^ 3 ∧
      ϵ + ϵ * (1 + ϵ) ^ 3 ≤ 9 * ϵ := by sorry

end RegevLWE.PeriodicGauss
