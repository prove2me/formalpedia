-- Prove2me | Theorems.Thm_VectorSpaceOpt_minimum_variance_W_form
-- name    : VectorSpaceOpt.minimum_variance_W_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T22:28:34.208124+00:00
-- url     : https://prove2.me/theorems/60cc42d5-944d-466b-b143-9bb80afa38d0
-- title:
--   The minimum-variance estimate in $W$-form
-- statement:
--   Consider measurements $y = W\beta + \varepsilon$, where $W$ is a known $m \times n$ matrix, $\beta$ is an $n$-dimensional **random** parameter vector (not an unknown constant), and $\varepsilon$ is an $m$-dimensional random error vector. Assume the second-moment matrices
--
--   $$E[\beta\beta^\top] = R, \qquad E[\varepsilon\varepsilon^\top] = Q, \qquad E[\varepsilon\beta^\top] = 0,$$
--
--   and that $W R W^\top + Q$ is nonsingular. Then the linear estimate of $\beta$ minimizing $E\|\hat\beta - \beta\|^2$ is
--
--   $$\hat\beta = R W^\top (W R W^\top + Q)^{-1}\, y,$$
--
--   with error covariance
--
--   $$E\big[(\beta - \hat\beta)(\beta - \hat\beta)^\top\big] = R - R W^\top (W R W^\top + Q)^{-1} W R .$$
--
--   This is the minimum-variance theorem specialized to the standard measurement model, and it is the form in which prior information about $\beta$ enters through its covariance $R$: it is the Bayesian counterpart of the Gauss–Markov estimate, which it reduces to in the limit of no prior information. The equivalent information form $(W^\top Q^{-1} W + R^{-1})^{-1} W^\top Q^{-1} y$ is stated separately.
--
--   **Formalization Note.** Optimality is asserted componentwise against every linear estimate $Ky$, matching the source's observation that the vector problem decomposes into one minimum norm problem per component. All second moments are uncentered and carry explicit integrability hypotheses; no distributional assumptions are used.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §4.5, Corollary 1, p. 88

import Mathlib
open Matrix MeasureTheory

namespace VectorSpaceOpt

theorem minimum_variance_W_form {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin n) ℝ)
    (β : Ω → Fin n → ℝ) (ε : Ω → Fin m → ℝ) (y : Ω → Fin m → ℝ)
    (hy : ∀ ω i, y ω i = W.mulVec (β ω) i + ε ω i)
    (hββ : ∀ i j : Fin n, Integrable (fun ω => β ω i * β ω j) μ)
    (hεε : ∀ i j : Fin m, Integrable (fun ω => ε ω i * ε ω j) μ)
    (hεβ : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => ε ω i * β ω j) μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : ∀ i j, ∫ ω, β ω i * β ω j ∂μ = R i j)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : ∀ i j, ∫ ω, ε ω i * ε ω j ∂μ = Q i j)
    (hcross : ∀ (i : Fin m) (j : Fin n), ∫ ω, ε ω i * β ω j ∂μ = 0)
    (hdet : IsUnit (W * R * Wᵀ + Q).det)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = R * Wᵀ * (W * R * Wᵀ + Q)⁻¹)
    (K : Matrix (Fin n) (Fin m) ℝ) :
    (∀ i, ∫ ω, (K₀.mulVec (y ω) i - β ω i) ^ 2 ∂μ ≤
          ∫ ω, (K.mulVec (y ω) i - β ω i) ^ 2 ∂μ) ∧
    (∀ i j, ∫ ω, (β ω i - K₀.mulVec (y ω) i) * (β ω j - K₀.mulVec (y ω) j) ∂μ =
      (R - R * Wᵀ * (W * R * Wᵀ + Q)⁻¹ * W * R) i j) := by sorry

end VectorSpaceOpt
