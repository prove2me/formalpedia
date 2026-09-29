-- Prove2me | Theorems.Thm_VectorSpaceOpt_gauss_markov
-- name    : VectorSpaceOpt.gauss_markov
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:28:08.599067+00:00
-- url     : https://prove2.me/theorems/25769f22-a867-467c-b202-b6e4c17419be
-- title:
--   The Gauss–Markov theorem
-- statement:
--   Consider an experiment yielding the $m$-dimensional data vector
--
--   $$y = W\beta + \varepsilon,$$
--
--   where $W$ is a known $m \times n$ matrix with linearly independent columns, $\beta \in \mathbb{R}^n$ is an unknown (non-random) parameter vector, and $\varepsilon$ is a random error vector with
--
--   $$E[\varepsilon] = 0, \qquad E[\varepsilon\varepsilon^\top] = Q \ \text{ positive definite}.$$
--
--   An estimate is **linear** if it has the form $\hat\beta = Ky$ for a constant matrix $K$, and **unbiased** if $E[\hat\beta] = \beta$ for every $\beta$ — which happens exactly when $KW = I$. Set
--
--   $$K_0 = (W^\top Q^{-1} W)^{-1} W^\top Q^{-1}, \qquad \hat\beta = K_0\, y.$$
--
--   Then:
--
--   1. $K_0 W = I$, so $\hat\beta$ is unbiased;
--   2. among all linear unbiased estimates $Ky$, the estimate $\hat\beta$ has minimum variance in **every component**, $E[(\hat\beta - \beta)_i^2] \le E[(Ky - \beta)_i^2]$ for each $i$;
--   3. its error covariance is $E\big[(\hat\beta - \beta)(\hat\beta - \beta)^\top\big] = (W^\top Q^{-1} W)^{-1}$.
--
--   Two remarks. Without the unbiasedness constraint the problem is ill-posed: the matrix minimizing $E\|Ky - \beta\|^2$ depends on the unknown $\beta$ itself, so no usable estimator results; requiring $KW = I$ removes that dependence, and the requirement turns out to be exactly unbiasedness. And when $Q = I$, the estimate coincides with the ordinary least-squares estimate — the two techniques are intimately related, but least squares is a single minimum norm problem while Gauss–Markov is $n$ of them.
--
--   **Formalization Note.** The probability space is abstract, with explicit integrability hypotheses for every first and second moment used; no independence, Gaussianity, or other distributional assumption enters. The claim quantifies over all competing $K$ satisfying $KW = I$, and the conclusions hold for every value of the unknown $\beta$.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §4.4, Theorem 1, p. 86

import Mathlib
open Matrix MeasureTheory

namespace VectorSpaceOpt

theorem gauss_markov {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin n) ℝ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (hW : LinearIndependent ℝ (fun j : Fin n => fun i : Fin m => W i j))
    (hQ : Q.PosDef)
    (ε : Ω → Fin m → ℝ)
    (hε1 : ∀ i : Fin m, Integrable (fun ω => ε ω i) μ)
    (hε2 : ∀ i j : Fin m, Integrable (fun ω => ε ω i * ε ω j) μ)
    (hmean : ∀ i : Fin m, ∫ ω, ε ω i ∂μ = 0)
    (hcov : ∀ i j : Fin m, ∫ ω, ε ω i * ε ω j ∂μ = Q i j)
    (β : Fin n → ℝ) (y : Ω → Fin m → ℝ)
    (hy : ∀ ω i, y ω i = W.mulVec β i + ε ω i)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = (Wᵀ * Q⁻¹ * W)⁻¹ * Wᵀ * Q⁻¹)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : K * W = 1) :
    K₀ * W = 1 ∧
    (∀ i, ∫ ω, (K₀.mulVec (y ω) i - β i) ^ 2 ∂μ ≤
          ∫ ω, (K.mulVec (y ω) i - β i) ^ 2 ∂μ) ∧
    (∀ i j, ∫ ω, (K₀.mulVec (y ω) i - β i) * (K₀.mulVec (y ω) j - β j) ∂μ =
      (Wᵀ * Q⁻¹ * W)⁻¹ i j) := by sorry

end VectorSpaceOpt
