-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_theorem_7
-- name    : ResidualsDRO.Wass.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:14:14.654665+00:00
-- url     : https://prove2.me/theorems/a97ad5d0-6e0f-4f20-a8b1-2861c18af4d6
-- title:
--   Theorem 7, p. 15 — Wasserstein ER-DRO with radius ζ_n(α, x) of (10) certifies P{g(ẑ^DRO_n(x); x) ≤ v̂^DRO_n(x)} ≥ 1 − α
-- statement:
--   **Finite sample certificate guarantee.** On a probability space $(\Omega,\mathbb P)$, let the training covariates $x^1,\dots,x^n$ ($n\ge1$) and the regression estimate $\hat f_n$ be random, and let the errors $\varepsilon^1,\dots,\varepsilon^n$ be i.i.d. with law $P_\varepsilon$ on $\mathbb R^{d_y}$ ($d_y\ge1$), with responses $y^i=f^*(x^i)+\varepsilon^i$. Let:
--
--   1. $\mathcal Y\subseteq\mathbb R^{d_y}$ be nonempty, closed and convex, with orthogonal projection $\mathrm{proj}_{\mathcal Y}$, containing every $f^*(x)+\varepsilon^i$ and the support of $P_{Y\mid X=x}$ (the law of $f^*(x)+\varepsilon$);
--   2. $\mathcal Z\subseteq\mathbb R^{d_z}$ be nonempty and compact, and $c:\mathbb R^{d_z}\times\mathbb R^{d_y}\to\mathbb R$ with $c(z,\cdot)$ measurable and $\mathbb E|c(z,f^*(x)+\varepsilon)|<\infty$ for $z\in\mathcal Z$; $g(z;x)=\mathbb E[c(z,f^*(x)+\varepsilon)]$;
--   3. $1\le p<a$ with Assumption 1, Assumption 2 at the covariate $x$ with constants $\kappa_{p,n}(\cdot,x)$, $p\ne d_y/2$, and $c_1,c_2>0$ constants for which the bound of Lemma 2 holds at $n$ and $x$;
--   4. $\alpha\in(0,1)$, and $\hat z^{DRO}_n(x)\in\mathcal Z$ an optimal solution of the ER-DRO problem (8) whose ambiguity set is the $p$-Wasserstein ball $\{Q\in\mathcal P(\mathcal Y): d_{W,p}(Q,\hat P^{ER}_n(x))\le\zeta_n(\alpha,x)\}$ with the radius $\zeta_n(\alpha,x)$ of (10), and $\hat v^{DRO}_n(x)$ its optimal value.
--
--   Then
--   $$\mathbb P\big\{g(\hat z^{DRO}_n(x);x)\le\hat v^{DRO}_n(x)\big\}\ge1-\alpha .$$
--
--   The optimal value of the residuals-based DRO problem is, with probability at least $1-\alpha$, an upper bound on the out-of-sample cost of its own solution, although the ambiguity set is centred at projected residual scenarios built from an estimated regression function rather than at samples from the conditional distribution.
--
--   **Formalization Note** The conclusion is stated in failure form, $\mathbb P\{g(\hat z^{DRO}_n(x);x)>\hat v^{DRO}_n(x)\}\le\alpha$, with $\mathbb P$ applied as an outer measure (for a measurable event this is the paper's statement). The paper's "for a.e. $x$" is handled pointwise: Assumption 2 and Lemma 2's bound are assumed at the given $x$. $\hat v^{DRO}_n(x)$ is an extended real and the worst case counts the distributions in the ball under which $c(z,\cdot)$ is integrable. **Correction:** the paper prints $\log(c_1\alpha^{-1})$ in $\kappa^{(2)}_{p,n}(\alpha)$; the derivation it states (setting Lemma 2's right-hand side to $\alpha/2$) gives $\log(2c_1\alpha^{-1})$, used here; with the printed formula the paper's proof yields only $3\alpha/2$. Lemma 2 is the paper's quotation of Fournier and Guillin (2015, Theorem 2), which is stated there for $W_p^p$; its conclusion enters as a hypothesis on $(c_1,c_2)$ exactly as the paper writes it.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 15, Theorem 7 (with (8), p. 9, and (10), p. 15)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_ResidualsDRO_Wass_Radius

open MeasureTheory ProbabilityTheory

namespace ResidualsDRO.Wass

/-- Theorem 7 (Finite sample certificate guarantee), p. 15. On a probability space `(Ω, P)`,
let the training covariates `xⁱ` and the regression estimate `f̂_n` be random, the errors
`ε¹, …, εⁿ` (`n ≥ 1`) i.i.d. with law `P_ε`, `yⁱ = f*(xⁱ) + εⁱ`; `𝒴 ⊆ ℝ^{d_y}` (`d_y ≥ 1`)
nonempty, closed and convex with orthogonal projection `proj`, containing `f*(x) + εⁱ` and the
support of `P_{Y|X=x}`; `𝒵` nonempty and compact; `c(z, ·)` measurable with
`E|c(z, f*(x) + ε)| < ∞` for `z ∈ 𝒵`. Let Assumptions 1 and 2 hold at the covariate `x`,
`p ≠ d_y/2`, and let `c₁, c₂ > 0` be constants for which Lemma 2 holds at `n` and `x`.
For `α ∈ (0, 1)`, let `ẑ^DRO_n(x)` be an optimal solution of the ER-DRO problem (8) with the
Wasserstein ball of (corrected) radius `ζ_n(α, x)` of (10) around `P̂^ER_n(x)`. Then
`P{g(ẑ^DRO_n(x); x) > v̂^DRO_n(x)} ≤ α`, i.e. `P{g(ẑ^DRO_n(x); x) ≤ v̂^DRO_n(x)} ≥ 1 - α`. -/
theorem theorem_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {dx dy dz n : ℕ} (hdy : 1 ≤ dy) (hn : 1 ≤ n)
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
    (hsupp : condLaw Pε fstar x 𝒴ᶜ = 0)
    (κ : ℝ → ℝ) (hA2 : Assumption2 P fstar fhat xs p x κ)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hL2 : Lemma2Bound P Pε fstar eps x dy p a c₁ c₂)
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) (h𝒵c : IsCompact 𝒵) (h𝒵n : 𝒵.Nonempty)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (hc_meas : ∀ z, Measurable (c z))
    (hc_int : ∀ z ∈ 𝒵, Integrable (fun e => c z (fstar x + e)) Pε)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (zhat : Ω → EuclideanSpace ℝ (Fin dz))
    (hopt : ∀ ω, zhat ω ∈ 𝒵 ∧ ∀ z ∈ 𝒵,
      WassersteinDRO.Duality.worstCaseRisk (radius κ c₁ c₂ a p dy n α) p 𝒴
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x) (c (zhat ω)) ≤
        WassersteinDRO.Duality.worstCaseRisk (radius κ c₁ c₂ a p dy n α) p 𝒴
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x) (c z)) :
    P {ω | ¬ ((trueObjective Pε fstar c x (zhat ω) : EReal) ≤
        erDROValue 𝒵 c (radius κ c₁ c₂ a p dy n α) p 𝒴
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x))} ≤
      ENNReal.ofReal α := by sorry

end ResidualsDRO.Wass
