-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_lemma_4
-- name    : ResidualsDRO.Wass.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:14:28.035711+00:00
-- url     : https://prove2.me/theorems/9276e8a5-ffa8-4ef3-9c40-2ef5bf9ad0fc
-- title:
--   Lemma 4, p. 14 — (1/n Σ‖ε̃ⁱ_n(x)‖^p)^{1/p} ≤ ‖f*(x) − f̂_n(x)‖ + (1/n Σ‖f*(xⁱ) − f̂_n(xⁱ)‖^p)^{1/p}
-- statement:
--   Let $p\ge1$ and $n\ge1$. Fix covariates $x^1,\dots,x^n$, errors $\varepsilon^i$ (responses $y^i=f^*(x^i)+\varepsilon^i$), a regression estimate $\hat f_n$ and a covariate $x$. Then
--   $$\Big(\frac1n\sum_{i=1}^n\|\tilde\varepsilon^i_n(x)\|^p\Big)^{1/p}\le\|f^*(x)-\hat f_n(x)\|+\Big(\frac1n\sum_{i=1}^n\|f^*(x^i)-\hat f_n(x^i)\|^p\Big)^{1/p}.$$
--
--   The power-mean size of the errors $\tilde\varepsilon^i_n(x)$ is bounded by the prediction error at $x$ plus the power-mean estimation error on the training covariates, the two quantities controlled by Assumption 2.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 14, Lemma 4

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Setting

open MeasureTheory

namespace ResidualsDRO.Wass

/-- Lemma 4, p. 14. Let `p ≥ 1` and `n ≥ 1`. For a data realization `(xⁱ, εⁱ)_{i ∈ [n]}`
(`yⁱ = f*(xⁱ) + εⁱ`), a regression estimate `f̂_n` and a covariate `x`,
`((1/n) Σᵢ ‖ε̃ⁱ_n(x)‖^p)^{1/p} ≤ ‖f*(x) - f̂_n(x)‖ + ((1/n) Σᵢ ‖f*(xⁱ) - f̂_n(xⁱ)‖^p)^{1/p}`. -/
theorem lemma_4 {dx dy n : ℕ} (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p)
    (fstar fhat : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → EuclideanSpace ℝ (Fin dx)) (eps : Fin n → EuclideanSpace ℝ (Fin dy))
    (x : EuclideanSpace ℝ (Fin dx)) :
    powerMean p (fun i => ‖epsTilde fstar fhat xs eps x i‖) ≤
      ‖fstar x - fhat x‖ + powerMean p (fun i => ‖fstar (xs i) - fhat (xs i)‖) := by sorry

end ResidualsDRO.Wass
