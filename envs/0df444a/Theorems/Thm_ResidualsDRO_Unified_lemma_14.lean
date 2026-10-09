-- Prove2me | Theorems.Thm_ResidualsDRO_Unified_lemma_14
-- name    : ResidualsDRO.Unified.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:05:29.25289+00:00
-- url     : https://prove2.me/theorems/6d09bb2c-12b4-4063-b19a-c30e6102aaeb
-- title:
--   Lemma 14, p. 22 — the three-term bound (12) on $\sup_z|\hat g^{ER}_{s,n}-g|$
-- statement:
--   Fix a covariate realization $x$, a sample size $n\ge1$ and a realization of the data. Let $\mathcal Y$ be nonempty, closed and convex with projection $\mathrm{proj}_{\mathcal Y}$, assume $f^*(x)+\varepsilon^i\in\mathcal Y$ for every $i$, let $\mathfrak P_n$ be a nonempty set of probability vectors in $\mathbb R^n$, let $\mu_n\ge0$, and suppose Assumption 9 holds with Lipschitz constants $L(z)$. Then
--
--   $$
--   \begin{aligned}
--   \sup_{z\in\mathcal Z}\bigl|\hat g^{ER}_{s,n}(z;x)-g(z;x)\bigr|
--   \le{}& \sup_{z\in\mathcal Z}L(z)\Bigl(\mu_n+\Bigl(\frac1n\sum_{i=1}^n\|\tilde\varepsilon^i_n(x)\|^2\Bigr)^{1/2}\Bigr)\sup_{p\in\mathfrak P_n}\Bigl(1+n\sum_{i=1}^n\Bigl(p_i-\frac1n\Bigr)^2\Bigr)^{1/2}\\
--   &+\sup_{p\in\mathfrak P_n}\Bigl(n\sum_{i=1}^n\Bigl(p_i-\frac1n\Bigr)^2\Bigr)^{1/2}\sup_{z\in\mathcal Z}\Bigl(\frac1n\sum_{i=1}^n c(z,f^*(x)+\varepsilon^i)^2\Bigr)^{1/2}\\
--   &+\sup_{z\in\mathcal Z}\bigl|g^*_n(z;x)-g(z;x)\bigr| .
--   \end{aligned}
--   $$
--
--   This deterministic inequality (12) splits the error of the ER-DRO objective into a regression term, a term measuring how far $\mathfrak P_n$ is from the uniform weights, and the error of the full-information SAA; every rate in §5 is read off from it.
--
--   **Formalization Note** Suprema over $z$ (and the left side) are computed in $[0,\infty]$, where $0\cdot\infty=0$; $\sup_z L(z)$ is the real supremum of the bounded set $L(\mathcal Z)$. The inequality is stated for one $n\ge1$ and one realization $\omega$ of the data.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 22, Lemma 14, inequality (12); proof App. A.6, pp. 44–45

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

/-- **Lemma 14** (Kannan–Bayraksan–Luedtke, p. 22; proof App. A.6, pp. 44–45). Under Assumption 9,
for each `n ≥ 1` and each realization `ω` of the data,
`sup_{z∈𝒵} |ĝ^ER_{s,n}(z;x) - g(z;x)| ≤ sup_z L(z) (μ_n + ((1/n)∑ᵢ‖ε̃ⁱ_n(x)‖²)^{1/2})
  · sup_{p∈𝔓_n} (1 + n∑ᵢ(pᵢ - 1/n)²)^{1/2}
  + sup_{p∈𝔓_n} (n∑ᵢ(pᵢ - 1/n)²)^{1/2} · sup_z ((1/n)∑ᵢ c(z, f*(x)+εⁱ)²)^{1/2}
  + sup_z |g*_n(z;x) - g(z;x)|`  (inequality (12)).
Suprema over `z` are taken in `[0, ∞]`; `sup_z L(z)` is `sSup (L '' 𝒵)`. -/
theorem lemma_14
    {dx dy dz : ℕ} {Ω : Type*}
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
    (μ : ℕ → ℝ) (hμ : ∀ n : ℕ, 0 ≤ μ n)
    (L : EuclideanSpace ℝ (Fin dz) → ℝ) (h9 : Assumption9 c D.𝒴 𝒵 L)
    (n : ℕ) (hn : 1 ≤ n) (ω : Ω)
    :
    (⨆ z ∈ 𝒵, ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z|) ≤
      ENNReal.ofReal (sSup (L '' 𝒵) *
          (μ n + Real.sqrt ((n : ℝ)⁻¹ * ∑ i : Fin n, ‖epsTilde D x n ω i‖ ^ 2)) *
          ⨆ p : 𝔓 n, Real.sqrt (1 + n * ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2)) +
        ENNReal.ofReal (⨆ p : 𝔓 n, Real.sqrt (n * ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2)) *
          (⨆ z ∈ 𝒵, ENNReal.ofReal
            (Real.sqrt ((n : ℝ)⁻¹ * ∑ i : Fin n, (c z (D.fstar x + D.eps i ω)) ^ 2))) +
        ⨆ z ∈ 𝒵, ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z| := by sorry

end ResidualsDRO.Unified
