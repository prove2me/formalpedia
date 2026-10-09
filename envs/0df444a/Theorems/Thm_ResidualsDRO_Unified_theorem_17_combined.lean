-- Prove2me | Theorems.Thm_ResidualsDRO_Unified_theorem_17_combined
-- name    : ResidualsDRO.Unified.theorem_17_combined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:05:30.931933+00:00
-- url     : https://prove2.me/theorems/42890e90-a408-4b52-852b-8dff38bd57a9
-- title:
--   Proof of Theorem 17, p. 24 — $\sup_z|\hat g^{ER}_{s,n}-g|=O_p(n^{-r/2})$
-- statement:
--   Under the assumptions of Theorem 17 (Assumptions 9, 13, 14 and 15, Assumption 12 with $\rho=1+r$, and $\mu_n(x)=C_\mu n^{-r/2}$ with $C_\mu>0$), the ER-DRO objective converges uniformly on $\mathcal Z$ to the true objective at the rate
--
--   $$
--   \sup_{z\in\mathcal Z}\bigl|\hat g^{ER}_{s,n}(z;x)-g(z;x)\bigr|=O_p\bigl(n^{-r/2}\bigr).
--   $$
--
--   The rates of the optimal value and of the out-of-sample cost in Theorem 17 follow from this uniform rate.
--
--   **Formalization Note** The supremum over $z$ is taken in $[0,\infty]$; $O_p$ is `IsBigOp`.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 24, proof of Theorem 17, combined display

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

/-- **Proof of Theorem 17, combined display** (p. 24). Under the assumptions of Theorem 17,
`sup_{z∈𝒵} |ĝ^ER_{s,n}(z;x) - g(z;x)| = O_p(n^{-r/2})`. -/
theorem theorem_17_combined
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
    :
    IsBigOp P (fun n ω => ⨆ z ∈ 𝒵,
        ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) := by sorry

end ResidualsDRO.Unified
