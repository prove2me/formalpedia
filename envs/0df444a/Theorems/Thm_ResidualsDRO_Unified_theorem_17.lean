-- Prove2me | Theorems.Thm_ResidualsDRO_Unified_theorem_17
-- name    : ResidualsDRO.Unified.theorem_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:05:35.44369+00:00
-- url     : https://prove2.me/theorems/11efcefc-ab54-41bb-8d28-ce54e35869ee
-- title:
--   Theorem 17 (Rate of convergence), p. 24 — $|\hat v^{DRO}_n-v^*|$ and $|g(\hat z^{DRO}_n)-v^*|$ are $O_p(n^{-r/2})$
-- statement:
--   Consider the empirical residuals-based DRO problem (8) with the unified sample-robust / same-support ambiguity set of §5, at a covariate realization $x$:
--
--   $$
--   \hat v^{DRO}_n(x)=\min_{z\in\mathcal Z}\hat g^{ER}_{s,n}(z;x),
--   $$
--
--   with optimal solution $\hat z^{DRO}_n(x)$, and let $v^*(x)=\min_{z\in\mathcal Z}g(z;x)$ be the optimal value of the true problem (3). Assume the standing conditions of the paper ($\mathcal Z$ nonempty and compact, $\mathcal Y$ nonempty closed convex containing $f^*(x)+\varepsilon^i$, $\mathbb E|c(z,f^*(x)+\varepsilon)|<\infty$, $\mathfrak P_n$ a nonempty set of probability vectors, and both minima attained). Suppose Assumptions 9, 13, 14 and 15 hold, Assumption 12 holds with $\rho=1+r$, and the radius satisfies $\mu_n(x)=C_\mu n^{-r/2}$ with $C_\mu>0$, where $r\in(0,1]$ is the constant of Assumption 15. Then
--
--   $$
--   \bigl|\hat v^{DRO}_n(x)-v^*(x)\bigr|=O_p\bigl(n^{-r/2}\bigr),\qquad
--   \bigl|g(\hat z^{DRO}_n(x);x)-v^*(x)\bigr|=O_p\bigl(n^{-r/2}\bigr).
--   $$
--
--   With $\rho=1+r$ the ER-DRO estimators inherit the convergence rate of the ER-SAA estimators: the robustification costs nothing in rate, and the rate is that of the regression step.
--
--   **Formalization Note** The paper's "for a.e. $x$" is read at a fixed $x$ at which every assumption holds. $\hat z^{DRO}_n$ is any selection of minimizers of $\hat g^{ER}_{s,n}(\cdot;x)$ over $\mathcal Z$ and $\hat v^{DRO}_n=\hat g^{ER}_{s,n}(\hat z^{DRO}_n;x)$; $v^*=g(z^*;x)$ for a minimizer $z^*$; the paper's standing assumptions guarantee both exist. The set $\mathfrak P_n$ is assumed nonempty and inside the probability simplex, the first part of (9); the limit clause of (9), about the family in the radius $\zeta$ at fixed $n$, is not used by the theorem and is dropped. No i.i.d. assumption is made. Assumption 12 is required for all large $n$ (at $n=1$ the printed equality cannot hold).
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 24, Theorem 17

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

/-- **Theorem 17 (Rate of convergence)** (Kannan–Bayraksan–Luedtke, p. 24). Suppose Assumptions 9,
13, 14 and 15 hold, Assumption 12 holds with `ρ = 1 + r`, and `μ_n(x) = C_μ n^{-r/2}` with
`C_μ > 0`. Then the optimal value `v̂^DRO_n(x) = ĝ^ER_{s,n}(ẑ^DRO_n(x); x)` and solution
`ẑ^DRO_n(x)` of the ER-DRO problem (8) satisfy
`|v̂^DRO_n(x) - v*(x)| = O_p(n^{-r/2})` and `|g(ẑ^DRO_n(x); x) - v*(x)| = O_p(n^{-r/2})`,
where `v*(x) = g(z*; x)` for a minimizer `z*` of the true problem (3). -/
theorem theorem_17
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx))
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) (h𝒵 : IsCompact 𝒵) (h𝒵ne : 𝒵.Nonempty)
    (h𝒴ne : D.𝒴.Nonempty) (h𝒴closed : IsClosed D.𝒴) (h𝒴convex : Convex ℝ D.𝒴)
    (hproj : IsProjection D.𝒴 D.proj)
    (hrange : ∀ (i : ℕ) (ω : Ω), D.fstar x + D.eps i ω ∈ D.𝒴)
    (hint : ∀ z ∈ 𝒵, Integrable (fun e => c z (D.fstar x + e)) Pε)
    (𝔓 : (n : ℕ) → Set (Fin n → ℝ))
    (h𝔓 : ∀ n, ∀ p ∈ 𝔓 n, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (h𝔓ne : ∀ n, 1 ≤ n → (𝔓 n).Nonempty)
    (r Cζ Cμ : ℝ) (μ : ℕ → ℝ) (hCμ : 0 < Cμ) (hμ : ∀ n : ℕ, μ n = Cμ * (n : ℝ) ^ (-(r / 2)))
    (L : EuclideanSpace ℝ (Fin dz) → ℝ) (h9 : Assumption9 c D.𝒴 𝒵 L)
    (h12 : Assumption12 𝔓 Cζ (1 + r))
    (h13 : Assumption13 P c D x Pε 𝒵)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (V : Ω' → C(𝒵, ℝ)) (h14 : Assumption14 P c D x Pε 𝒵 P' V)
    (h15 : Assumption15 P D x r)
    (zhat : ℕ → Ω → EuclideanSpace ℝ (Fin dz))
    (hzhat : ∀ n ω, zhat n ω ∈ 𝒵 ∧
      ∀ z ∈ 𝒵, ghatER c D x 𝔓 μ n ω (zhat n ω) ≤ ghatER c D x 𝔓 μ n ω z)
    (zstar : EuclideanSpace ℝ (Fin dz))
    (hzstar : zstar ∈ 𝒵 ∧ ∀ z ∈ 𝒵, gTrue c D x Pε zstar ≤ gTrue c D x Pε z)
    :
    IsBigOp P (fun n ω => ENNReal.ofReal
        |ghatER c D x 𝔓 μ n ω (zhat n ω) - gTrue c D x Pε zstar|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) ∧
      IsBigOp P (fun n ω => ENNReal.ofReal
        |gTrue c D x Pε (zhat n ω) - gTrue c D x Pε zstar|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) := by sorry

end ResidualsDRO.Unified
