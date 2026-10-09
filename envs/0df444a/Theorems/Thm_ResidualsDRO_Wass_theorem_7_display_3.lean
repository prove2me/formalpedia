-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_theorem_7_display_3
-- name    : ResidualsDRO.Wass.theorem_7_display_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:14:21.173979+00:00
-- url     : https://prove2.me/theorems/1c82e407-5412-414e-a328-50ab6f3267a6
-- title:
--   Proof of Theorem 7, display 3, p. 15 — P{d_{W,p}(P̂^ER_n(x), P_{Y|X=x}) > ζ_n(α, x)} ≤ α
-- statement:
--   Assume the setting of Theorem 7: on a probability space $(\Omega,\mathbb P)$ the training covariates $x^i$ and the regression estimate $\hat f_n$ are random, the errors $\varepsilon^1,\dots,\varepsilon^n$ ($n\ge1$) are i.i.d. with law $P_\varepsilon$, $y^i=f^*(x^i)+\varepsilon^i$; $\mathcal Y\subseteq\mathbb R^{d_y}$ ($d_y\ge1$) is nonempty, closed and convex with orthogonal projection $\mathrm{proj}_{\mathcal Y}$ and contains $f^*(x)+\varepsilon^i$; Assumptions 1 and 2 hold at the covariate $x$ with $1\le p$; $p\ne d_y/2$; and $c_1,c_2>0$ are constants for which the bound of Lemma 2 holds at $n$ and $x$. Then for every $\alpha\in(0,1)$,
--   $$\mathbb P\big\{d_{W,p}(\hat P^{ER}_n(x),P_{Y\mid X=x})>\zeta_n(\alpha,x)\big\}\le\alpha,$$
--   with $\zeta_n(\alpha,x)$ the radius (10) (second term built from $\log(2c_1\alpha^{-1})$).
--
--   The conditional distribution of $Y$ given $X=x$ lies in the Wasserstein ball of radius $\zeta_n(\alpha,x)$ around the estimated empirical distribution with probability at least $1-\alpha$; Theorem 7 follows from this.
--
--   **Formalization Note** The paper's "for a.e. $x$" is handled pointwise; probabilities are outer measures; the radius uses the corrected $\kappa^{(2)}_{p,n}(\alpha)$ (the paper prints $\log(c_1\alpha^{-1})$).
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 15, proof of Theorem 7, third display

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_ResidualsDRO_Wass_Radius

open MeasureTheory ProbabilityTheory

namespace ResidualsDRO.Wass

/-- Proof of Theorem 7, display 3, p. 15. Setting of Theorem 7: on a probability space
`(Ω, P)`, random training covariates `xⁱ`, i.i.d. errors `εⁱ ∼ P_ε` (`n ≥ 1`), responses
`yⁱ = f*(xⁱ) + εⁱ`, a random regression estimate `f̂_n`; `𝒴 ⊆ ℝ^{d_y}` nonempty, closed, convex
with orthogonal projection `proj`, containing `f*(x) + εⁱ`; Assumptions 1 and 2 at the
covariate `x`; `p ≠ d_y/2`; constants `c₁, c₂ > 0` for which Lemma 2 holds at `n` and `x`. Then
for `α ∈ (0, 1)`, with the (corrected) radius `ζ_n(α, x)` of (10),
`P{d_{W,p}(P̂^ER_n(x), P_{Y|X=x}) > ζ_n(α, x)} ≤ α`. -/
theorem theorem_7_display_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {dx dy n : ℕ} (hdy : 1 ≤ dy) (hn : 1 ≤ n)
    (p a : ℝ) (hp : 1 ≤ p) (hpdy : p ≠ (dy : ℝ) / 2)
    (𝒴 : Set (EuclideanSpace ℝ (Fin dy)))
    (h𝒴c : IsClosed 𝒴) (h𝒴v : Convex ℝ 𝒴) (h𝒴n : 𝒴.Nonempty)
    (proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy))
    (hproj : IsNearestPointProj 𝒴 proj)
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (hA1 : Assumption1 Pε p a)
    (fstar : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (fhat : Ω → EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → Ω → EuclideanSpace ℝ (Fin dx))
    (eps : Fin n → Ω → EuclideanSpace ℝ (Fin dy)) (heps_meas : ∀ i, Measurable (eps i))
    (heps_indep : iIndepFun eps P) (heps_law : ∀ i, P.map (eps i) = Pε)
    (x : EuclideanSpace ℝ (Fin dx)) (hY : ∀ i ω, fstar x + eps i ω ∈ 𝒴)
    (κ : ℝ → ℝ) (hA2 : Assumption2 P fstar fhat xs p x κ)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hL2 : Lemma2Bound P Pε fstar eps x dy p a c₁ c₂)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    P {ω | ENNReal.ofReal (radius κ c₁ c₂ a p dy n α) <
        WassersteinDRO.Duality.wassersteinDistance p
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x)
          (condLaw Pε fstar x)} ≤
      ENNReal.ofReal α := by sorry

end ResidualsDRO.Wass
