-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_lemma_6
-- name    : ResidualsDRO.Wass.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:14:37.288048+00:00
-- url     : https://prove2.me/theorems/e4c0939f-0fe2-49b1-960b-9fa3c69e3d26
-- title:
--   Lemma 6, p. 14 — P{(1/n Σ‖ε̃ⁱ_n(x)‖^p)^{1/p} > 2κ_{p,n}(α/4, x)} ≤ α/2
-- statement:
--   On a probability space $(\Omega,\mathbb P)$, let the training covariates $x^1,\dots,x^n$ ($n\ge1$), the errors $\varepsilon^1,\dots,\varepsilon^n$ and the regression estimate $\hat f_n$ be random, with responses $y^i=f^*(x^i)+\varepsilon^i$. Let $p\ge1$ and let Assumption 2 hold at the covariate $x$ with constants $\kappa_{p,n}(\cdot,x)$. Then for every $\alpha\in(0,1)$,
--   $$\mathbb P\Big\{\Big(\frac1n\sum_{i=1}^n\|\tilde\varepsilon^i_n(x)\|^p\Big)^{1/p}>2\kappa_{p,n}\big(\tfrac\alpha4,x\big)\Big\}\le\frac\alpha2.$$
--
--   This is the finite sample bound on the regression part of the radius: $\kappa^{(1)}_{p,n}(\alpha,x)=2\kappa_{p,n}(\alpha/4,x)$ is exceeded with probability at most $\alpha/2$.
--
--   **Formalization Note** The paper's "for a.e. $x$" is handled pointwise: Assumption 2 is assumed at the given $x$. Probabilities are outer measures.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 14, Lemma 6

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_ResidualsDRO_Wass_Radius

open MeasureTheory

namespace ResidualsDRO.Wass

/-- Lemma 6, p. 14. On a probability space `(Ω, P)`, let the training covariates `xⁱ(ω)`, the
errors `εⁱ(ω)` and the regression estimate `f̂_n(ω)` be random, `p ≥ 1`, `n ≥ 1`, and let
Assumption 2 hold at the covariate `x` with constants `κ_{p,n}(·, x)`. Then for `α ∈ (0, 1)`,
`P{((1/n) Σᵢ ‖ε̃ⁱ_n(x)‖^p)^{1/p} > 2κ_{p,n}(α/4, x)} ≤ α/2`. -/
theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {dx dy n : ℕ} (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p)
    (fstar : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (fhat : Ω → EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → Ω → EuclideanSpace ℝ (Fin dx)) (eps : Fin n → Ω → EuclideanSpace ℝ (Fin dy))
    (x : EuclideanSpace ℝ (Fin dx)) (κ : ℝ → ℝ) (hA2 : Assumption2 P fstar fhat xs p x κ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    P {ω | 2 * κ (α / 4) <
        powerMean p (fun i => ‖epsTilde fstar (fhat ω) (fun j => xs j ω) (fun j => eps j ω) x i‖)} ≤
      ENNReal.ofReal (α / 2) := by sorry

end ResidualsDRO.Wass
