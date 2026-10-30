-- Prove2me | Theorems.Thm_PrivAcq_Central_mse_linear_estimator
-- name    : PrivAcq.Central.mse_linear_estimator
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:41.778971+00:00
-- url     : https://prove2.me/theorems/b52bf708-d2a2-47cc-89d9-61ebe6d523e5
-- title:
--   p. 18 (display before (24)) — the MSE of $\sum_i w_i x_i + \mathrm{Laplace}(1/\eta)$ is $2/\eta^2 + \sum_i w_i^2\,\mathrm{VAR}$
-- statement:
--   On a probability space, let $Z_1,\dots,Z_n$ be identically distributed random variables with mean $0$, variance $\mathrm{VAR}$ and $|Z_i| \le \tfrac12$, and let $L$ be a random variable with law $\mathrm{Laplace}(1/\eta)$, $\eta > 0$, such that $Z_1,\dots,Z_n, L$ are mutually independent. Let $\theta \in \mathbb R$, let $X_i = \theta + Z_i$, and let $w_1,\dots,w_n$ be weights with $\sum_i w_i = 1$. Then the estimator $\hat\theta = \sum_i w_i X_i + L$ has mean square error
--   $$
--   \mathbb E\big[(\hat\theta - \theta)^2\big] = \frac{2}{\eta^2} + \sum_{i=1}^n w_i^2\,\mathrm{VAR}.
--   $$
--
--   This closed form is the MSE used throughout the mechanism design problem of the central setting; it is the formula `mse` of the model file.
--
--   **Formalization Note** Independence is stated for the family indexed by `Option (Fin n)` with `none ↦ L` and `some i ↦ Z i`; the law of $L$ is the published `PrivLearn.Generic.laplace (1/η)` (density $\frac{\eta}{2}e^{-\eta|x|}$).
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, p. 18 (display before (24)); restated in the proof of Theorem 3, p. 44; data model p. 7

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

namespace PrivAcq.Central

open MeasureTheory ProbabilityTheory

theorem mse_linear_estimator {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (θ var η : ℝ) (hη : 0 < η) (w : Fin n → ℝ)
    (hsum : ∑ i, w i = 1) (Z : Fin n → Ω → ℝ) (L : Ω → ℝ)
    (hZmeas : ∀ i, Measurable (Z i)) (hLmeas : Measurable L)
    (hindep : iIndepFun (fun o : Option (Fin n) => Option.elim o L Z) P)
    (hident : ∀ i j, IdentDistrib (Z i) (Z j) P P)
    (hbdd : ∀ i ω, |Z i ω| ≤ 1 / 2)
    (hmean : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (hvar : ∀ i, variance (Z i) P = var)
    (hL : P.map L = PrivLearn.Generic.laplace (1 / η)) :
    ∫ ω, (∑ i, w i * (θ + Z i ω) + L ω - θ) ^ 2 ∂P = 2 / η ^ 2 + ∑ i, (w i) ^ 2 * var := by sorry

end PrivAcq.Central
