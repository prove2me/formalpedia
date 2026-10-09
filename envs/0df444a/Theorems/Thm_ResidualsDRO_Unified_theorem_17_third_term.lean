-- Prove2me | Theorems.Thm_ResidualsDRO_Unified_theorem_17_third_term
-- name    : ResidualsDRO.Unified.theorem_17_third_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:05:21.903702+00:00
-- url     : https://prove2.me/theorems/c935f14a-ac87-458c-9619-623b3e0fe70f
-- title:
--   Proof of Theorem 17, p. 24 — the FCLT gives $\sup_z|g^*_n-g|=O_p(n^{-1/2})$
-- statement:
--   Let $\mathcal Z$ be nonempty and compact and suppose Assumption 14 holds: $g^*_n(\cdot;x)$ and $g(\cdot;x)$ are continuous on $\mathcal Z$ and $\sqrt n\,(g^*_n(\cdot;x)-g(\cdot;x))$ converges in distribution in $C(\mathcal Z)$ to a random element $V(\cdot;x)$. Then
--
--   $$
--   \sup_{z\in\mathcal Z}\bigl|g^*_n(z;x)-g(z;x)\bigr|=O_p\bigl(n^{-1/2}\bigr).
--   $$
--
--   This is the full-information part of the error: the SAA objective built from the true errors converges uniformly at the parametric rate.
--
--   **Formalization Note** The supremum over $z$ is taken in $[0,\infty]$; $O_p$ is `IsBigOp`; convergence in distribution is Mathlib's `TendstoInDistribution` for the Borel $\sigma$-algebra of $C(\mathcal Z)$.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 24, proof of Theorem 17, consequence of Assumption 14

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

/-- **Proof of Theorem 17, FCLT step** (p. 24). Assumption 14 implies
`sup_{z∈𝒵} |g*_n(z;x) - g(z;x)| = O_p(n^{-1/2})`. -/
theorem theorem_17_third_term
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx))
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) (h𝒵 : IsCompact 𝒵) (h𝒵ne : 𝒵.Nonempty)
    (h𝒴ne : D.𝒴.Nonempty) (h𝒴closed : IsClosed D.𝒴) (h𝒴convex : Convex ℝ D.𝒴)
    (hproj : IsProjection D.𝒴 D.proj)
    (hrange : ∀ (i : ℕ) (ω : Ω), D.fstar x + D.eps i ω ∈ D.𝒴)
    (hint : ∀ z ∈ 𝒵, Integrable (fun e => c z (D.fstar x + e)) Pε)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (V : Ω' → C(𝒵, ℝ)) (h14 : Assumption14 P c D x Pε 𝒵 P' V)
    :
    IsBigOp P (fun n ω => ⨆ z ∈ 𝒵,
        ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z|) (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end ResidualsDRO.Unified
