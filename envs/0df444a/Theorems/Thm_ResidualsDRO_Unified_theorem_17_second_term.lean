-- Prove2me | Theorems.Thm_ResidualsDRO_Unified_theorem_17_second_term
-- name    : ResidualsDRO.Unified.theorem_17_second_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:05:24.089209+00:00
-- url     : https://prove2.me/theorems/ef94631a-c895-4866-8d73-2626c5210f8e
-- title:
--   Proof of Theorem 17, p. 24 — $\sup_z|g^*_{s,n}-g^*_n|=O_p(n^{-r/2})$
-- statement:
--   In the setting of Theorem 17, suppose Assumption 12 holds with $\rho=1+r$ for some $r>0$ and Assumption 13 holds. Then
--
--   $$
--   \sup_{z\in\mathcal Z}\bigl|g^*_{s,n}(z;x)-g^*_n(z;x)\bigr|=O_p\bigl(n^{-r/2}\bigr).
--   $$
--
--   This is the price of reweighting: the worst case over the probability set $\mathfrak P_n$ differs from the uniform full-information average by at most the rate at which $\mathfrak P_n$ shrinks to the uniform weights.
--
--   **Formalization Note** The supremum over $z$ is taken in $[0,\infty]$; $O_p$ is `IsBigOp`.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 24, proof of Theorem 17, second display

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

/-- **Proof of Theorem 17, second display** (p. 24). Under Assumptions 12 (with `ρ = 1 + r`) and 13,
`sup_{z∈𝒵} |g*_{s,n}(z;x) - g*_n(z;x)| = O_p(n^{-r/2})`. -/
theorem theorem_17_second_term
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
    (r Cζ : ℝ)
    (h12 : Assumption12 𝔓 Cζ (1 + r))
    (h13 : Assumption13 P c D x Pε 𝒵)
    :
    IsBigOp P (fun n ω => ⨆ z ∈ 𝒵,
        ENNReal.ofReal |gstarS c D x 𝔓 n ω z - gstarN c D x n ω z|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) := by sorry

end ResidualsDRO.Unified
