-- Prove2me | Theorems.Thm_VectorSpaceOpt_minimum_variance_estimate
-- name    : VectorSpaceOpt.minimum_variance_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:27:35.92575+00:00
-- url     : https://prove2.me/theorems/9146d417-b772-4792-88b9-8d2be7f29140
-- title:
--   The minimum-variance estimate
-- statement:
--   Let $y$ and $b$ be random vectors, of dimensions $m$ and $n$ and not necessarily of the same dimension, with second-moment matrices
--
--   $$S_{yy} = E[y y^\top], \qquad S_{by} = E[b y^\top], \qquad S_{bb} = E[b b^\top],$$
--
--   and assume $S_{yy}$ is invertible. Then the linear estimate of $b$ based on $y$ that minimizes the error second moment is
--
--   $$\hat b = S_{by}\, S_{yy}^{-1}\, y,$$
--
--   and its error covariance is
--
--   $$E\big[(b - \hat b)(b - \hat b)^\top\big] = S_{bb} - S_{by}\, S_{yy}^{-1}\, S_{by}^\top.$$
--
--   Optimality holds **componentwise**: for each $i$, no linear estimate $Ky$ achieves a smaller $E[((Ky)_i - b_i)^2]$ than $\hat b$ does.
--
--   This is the normal equations in disguise. The problem decomposes into one unconstrained minimum norm problem per component of $b$ — project $b_i$ onto the subspace of random variables spanned by the components of $y$ — and writing the $n$ systems of normal equations simultaneously in matrix form gives $S_{yy} K^\top = S_{by}^\top$, hence the formula. Unlike the Gauss–Markov setting, $b$ here is itself random with known statistics, so no unbiasedness constraint is imposed.
--
--   **Formalization Note.** All moments are **uncentered** — no means are subtracted anywhere, and nothing is assumed about $E[y]$ or $E[b]$ individually. Estimators are strictly linear ($Ky$, no additive constant); the affine extension is the source's Problem 6 and is not claimed here.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §4.5, Theorem 1, pp. 87–88

import Mathlib
open Matrix MeasureTheory

namespace VectorSpaceOpt

theorem minimum_variance_estimate {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (hbb : ∀ i j : Fin n, Integrable (fun ω => b ω i * b ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (Sby : Matrix (Fin n) (Fin m) ℝ) (hSby : ∀ i j, ∫ ω, b ω i * y ω j ∂μ = Sby i j)
    (Sbb : Matrix (Fin n) (Fin n) ℝ) (hSbb : ∀ i j, ∫ ω, b ω i * b ω j ∂μ = Sbb i j)
    (hdet : IsUnit Syy.det)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = Sby * Syy⁻¹)
    (K : Matrix (Fin n) (Fin m) ℝ) :
    (∀ i, ∫ ω, (K₀.mulVec (y ω) i - b ω i) ^ 2 ∂μ ≤
          ∫ ω, (K.mulVec (y ω) i - b ω i) ^ 2 ∂μ) ∧
    (∀ i j, ∫ ω, (b ω i - K₀.mulVec (y ω) i) * (b ω j - K₀.mulVec (y ω) j) ∂μ =
      (Sbb - Sby * Syy⁻¹ * Sbyᵀ) i j) := by sorry

end VectorSpaceOpt
