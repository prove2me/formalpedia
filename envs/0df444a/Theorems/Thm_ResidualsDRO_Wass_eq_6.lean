-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_eq_6
-- name    : ResidualsDRO.Wass.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:12:53.766408+00:00
-- url     : https://prove2.me/theorems/8d108d4c-ef4c-4294-aff4-22718c0c490e
-- title:
--   (6), p. 8 — ‖proj_𝒴(f̂_n(x) + ε̂ⁱ_n) − (f*(x) + εⁱ)‖ ≤ ‖ε̃ⁱ_n(x)‖
-- statement:
--   Let $\mathcal Y\subseteq\mathbb R^{d_y}$ be nonempty, closed and convex, with orthogonal projection $\mathrm{proj}_{\mathcal Y}$. Fix covariates $x^1,\dots,x^n$, errors $\varepsilon^1,\dots,\varepsilon^n$ with responses $y^i=f^*(x^i)+\varepsilon^i$, a regression estimate $\hat f_n$ with residuals $\hat\varepsilon^i_n=y^i-\hat f_n(x^i)$, and a covariate $x$ such that $f^*(x)+\varepsilon^i\in\mathcal Y$ for every $i$. Then for every $i\in[n]$,
--   $$\big\|\mathrm{proj}_{\mathcal Y}(\hat f_n(x)+\hat\varepsilon^i_n)-(f^*(x)+\varepsilon^i)\big\|\le\|\tilde\varepsilon^i_n(x)\|,$$
--   where $\tilde\varepsilon^i_n(x)=(\hat f_n(x)+\hat\varepsilon^i_n)-(f^*(x)+\varepsilon^i)=(\hat f_n(x)-f^*(x))+(f^*(x^i)-\hat f_n(x^i))$.
--
--   Each projected scenario of the estimated empirical distribution lies within $\|\tilde\varepsilon^i_n(x)\|$ of the corresponding scenario of the true empirical distribution; $\tilde\varepsilon^i_n(x)$ is the prediction error at $x$ plus the estimation error at $x^i$. This is the key inequality behind Lemma 3.
--
--   **Formalization Note** The paper writes "$\forall i\in[n]$" and "for each $x$"; the hypothesis $f^*(x)+\varepsilon^i\in\mathcal Y$, which the paper takes from $\mathcal Y$ containing the range of $Y$, is stated explicitly. Both conclusions (the inequality and the identity for $\tilde\varepsilon^i_n(x)$) are stated.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 8, (6) and footnote 4

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Setting

open MeasureTheory

namespace ResidualsDRO.Wass

/-- (6), p. 8. Let `𝒴 ⊆ ℝ^{d_y}` be nonempty, closed and convex and `proj` the orthogonal
projection onto `𝒴` (nearest-point map). For a data realization `(xⁱ, εⁱ)_{i ∈ [n]}` with
`yⁱ = f*(xⁱ) + εⁱ`, a regression estimate `f̂_n` and a covariate `x` with `f*(x) + εⁱ ∈ 𝒴`
for all `i`:
`‖proj_𝒴(f̂_n(x) + ε̂ⁱ_n) - (f*(x) + εⁱ)‖ ≤ ‖ε̃ⁱ_n(x)‖` for every `i ∈ [n]`, and
`ε̃ⁱ_n(x) = (f̂_n(x) - f*(x)) + (f*(xⁱ) - f̂_n(xⁱ))`. -/
theorem eq_6 {dx dy n : ℕ} (𝒴 : Set (EuclideanSpace ℝ (Fin dy)))
    (h𝒴c : IsClosed 𝒴) (h𝒴v : Convex ℝ 𝒴) (h𝒴n : 𝒴.Nonempty)
    (proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy))
    (hproj : IsNearestPointProj 𝒴 proj)
    (fstar fhat : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → EuclideanSpace ℝ (Fin dx)) (eps : Fin n → EuclideanSpace ℝ (Fin dy))
    (x : EuclideanSpace ℝ (Fin dx)) (hY : ∀ i, fstar x + eps i ∈ 𝒴) (i : Fin n) :
    ‖proj (fhat x + residual fstar fhat xs eps i) - (fstar x + eps i)‖ ≤
        ‖epsTilde fstar fhat xs eps x i‖ ∧
      epsTilde fstar fhat xs eps x i = (fhat x - fstar x) + (fstar (xs i) - fhat (xs i)) := by sorry

end ResidualsDRO.Wass
