-- Prove2me | Theorems.Thm_ResidualsDRO_Unified_theorem_17_first_term
-- name    : ResidualsDRO.Unified.theorem_17_first_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:05:50.566358+00:00
-- url     : https://prove2.me/theorems/eb0195d5-b73c-4f70-9411-0df7d4684e1a
-- title:
--   Proof of Theorem 17, p. 24 — $\sup_z|\hat g^{ER}_{s,n}-g^*_{s,n}|=O_p(n^{-r/2})$
-- statement:
--   In the setting of Theorem 17, suppose Assumption 9 holds, Assumption 12 holds with $\rho=1+r$, Assumption 15 holds with constant $r\in(0,1]$, and the sample-robust radius is $\mu_n(x)=C_\mu n^{-r/2}$ with $C_\mu>0$. Then
--
--   $$
--   \sup_{z\in\mathcal Z}\bigl|\hat g^{ER}_{s,n}(z;x)-g^*_{s,n}(z;x)\bigr|=O_p\bigl(n^{-r/2}\bigr).
--   $$
--
--   This is the regression part of the error: replacing the true scenarios $f^*(x)+\varepsilon^i$ by sample-robust balls around the projected residual scenarios costs no more than the regression rate.
--
--   **Formalization Note** The supremum over $z$ is taken in $[0,\infty]$; $O_p$ is `IsBigOp`. The balls are centred at the projected residual scenarios $\mathrm{proj}_{\mathcal Y}(\hat f_n(x)+\hat\varepsilon^i_n)$, as in the paper.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 24, proof of Theorem 17, first display

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

/-- **Proof of Theorem 17, first display** (p. 24). Under Assumptions 9, 12 (with `ρ = 1 + r`)
and 15 and `μ_n = C_μ n^{-r/2}`,
`sup_{z∈𝒵} |ĝ^ER_{s,n}(z;x) - g*_{s,n}(z;x)| = O_p(n^{-r/2})`. -/
theorem theorem_17_first_term
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
    (h15 : Assumption15 P D x r)
    :
    IsBigOp P (fun n ω => ⨆ z ∈ 𝒵,
        ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gstarS c D x 𝔓 n ω z|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) := by sorry

end ResidualsDRO.Unified
