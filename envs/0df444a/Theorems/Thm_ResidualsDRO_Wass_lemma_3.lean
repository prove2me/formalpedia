-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_lemma_3
-- name    : ResidualsDRO.Wass.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:12:58.28767+00:00
-- url     : https://prove2.me/theorems/aaed1f18-3052-4e61-8c32-79da8b8ec55c
-- title:
--   Lemma 3, p. 13 — d_{W,p}(P̂^ER_n(x), P_{Y|X=x}) ≤ (1/n Σ‖ε̃ⁱ_n(x)‖^p)^{1/p} + d_{W,p}(P*_n(x), P_{Y|X=x})
-- statement:
--   Let $p\ge1$, $n\ge1$, $\mathcal Y\subseteq\mathbb R^{d_y}$ nonempty, closed and convex with orthogonal projection $\mathrm{proj}_{\mathcal Y}$, and $P_\varepsilon$ a probability distribution on $\mathbb R^{d_y}$. Fix covariates $x^i$, errors $\varepsilon^i$ (responses $y^i=f^*(x^i)+\varepsilon^i$), a regression estimate $\hat f_n$ and a covariate $x$ with $f^*(x)+\varepsilon^i\in\mathcal Y$ for all $i\in[n]$. Then
--   $$d_{W,p}\big(\hat P^{ER}_n(x),P_{Y\mid X=x}\big)\le\Big(\frac1n\sum_{i=1}^n\|\tilde\varepsilon^i_n(x)\|^p\Big)^{1/p}+d_{W,p}\big(P^*_n(x),P_{Y\mid X=x}\big),$$
--   where $P^*_n(x)$ and $\hat P^{ER}_n(x)$ are the true and the estimated empirical distributions and $P_{Y\mid X=x}$ is the law of $f^*(x)+\varepsilon$.
--
--   The Wasserstein distance from the estimated empirical distribution to the conditional distribution is at most the power mean of the errors $\tilde\varepsilon^i_n(x)$ plus the sampling error of the true empirical distribution. It splits the analysis of Theorem 7 into a regression part and a concentration part.
--
--   **Formalization Note** Distances are in $[0,+\infty]$ (the published `wassersteinDistance`), so no moment condition on $P_\varepsilon$ is needed; the power mean is embedded by `ENNReal.ofReal`.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 13, Lemma 3

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_ResidualsDRO_Wass_Setting

open MeasureTheory

namespace ResidualsDRO.Wass

/-- Lemma 3, p. 13. Let `p ≥ 1`, `n ≥ 1`, `𝒴 ⊆ ℝ^{d_y}` nonempty, closed and convex with
orthogonal projection `proj`, `P_ε` a probability distribution of the errors, and fix a data
realization `(xⁱ, εⁱ)_{i ∈ [n]}` (`yⁱ = f*(xⁱ) + εⁱ`), a regression estimate `f̂_n` and a
covariate `x` with `f*(x) + εⁱ ∈ 𝒴` for all `i`. Then
`d_{W,p}(P̂^ER_n(x), P_{Y|X=x}) ≤ ((1/n) Σᵢ ‖ε̃ⁱ_n(x)‖^p)^{1/p} + d_{W,p}(P*_n(x), P_{Y|X=x})`
(in `[0, +∞]`). -/
theorem lemma_3 {dx dy n : ℕ} (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p)
    (𝒴 : Set (EuclideanSpace ℝ (Fin dy)))
    (h𝒴c : IsClosed 𝒴) (h𝒴v : Convex ℝ 𝒴) (h𝒴n : 𝒴.Nonempty)
    (proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy))
    (hproj : IsNearestPointProj 𝒴 proj)
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (fstar fhat : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → EuclideanSpace ℝ (Fin dx)) (eps : Fin n → EuclideanSpace ℝ (Fin dy))
    (x : EuclideanSpace ℝ (Fin dx)) (hY : ∀ i, fstar x + eps i ∈ 𝒴) :
    WassersteinDRO.Duality.wassersteinDistance p (erEmpirical proj fstar fhat xs eps x)
        (condLaw Pε fstar x) ≤
      ENNReal.ofReal (powerMean p (fun i => ‖epsTilde fstar fhat xs eps x i‖)) +
        WassersteinDRO.Duality.wassersteinDistance p (trueEmpirical fstar eps x)
          (condLaw Pε fstar x) := by sorry

end ResidualsDRO.Wass
