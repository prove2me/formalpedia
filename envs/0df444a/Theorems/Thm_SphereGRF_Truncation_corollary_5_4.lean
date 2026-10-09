-- Prove2me | Theorems.Thm_SphereGRF_Truncation_corollary_5_4
-- name    : SphereGRF.Truncation.corollary_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:36:31.720448+00:00
-- url     : https://prove2.me/theorems/9f0b5b1c-989b-4db0-8227-e62ad1f9d775
-- title:
--   Corollary 5.4, p. 28 — almost-sure KL truncation rate
-- statement:
--   Let $T$ be the centered isotropic Gaussian field given by the KL series on $S^2$, and let $T^\kappa$ be its truncation through degree $\kappa$. Assume $A_\ell\ge0$, $C>0$, $\alpha>2$, $\ell_0\ge1$, and $A_\ell\le C\ell^{-\alpha}$ whenever $\ell>\ell_0$. Then $T^\kappa\to T$ almost surely in $L^2(S^2)$. For every $\beta<(\alpha-2)/2$, almost every sample eventually satisfies
--
--   $$
--   \|T-T^\kappa\|_{L^2(S^2)}\le\kappa^{-\beta}.
--   $$
--
--   This turns the uniform family of finite-moment truncation estimates into a pathwise convergence rate.
--
--   **Formalization Note** Convergence and the bound are measured in the spatial $L^2$ norm, not pointwise on the sphere. The exceptional null set may depend on $\beta$. The field is the page-25 series representation; Lemma 5.1 provides its identification in law with a centered isotropic field.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Corollary 5.4, p. 28

import Mathlib
import Definitions.Def_SphereGRF_Truncation_Setting

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace SphereGRF.Truncation

theorem corollary_5_4 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → ℝ) (X : ℕ → ℕ → Fin 2 → Ω → ℝ)
    (C α : ℝ) (ℓ₀ : ℕ)
    (hA0 : ∀ ℓ, 0 ≤ A ℓ) (hC : 0 < C) (hα : 2 < α) (hℓ₀ : 1 ≤ ℓ₀)
    (hdec : ∀ ℓ : ℕ, ℓ₀ < ℓ → A ℓ ≤ C * (ℓ : ℝ) ^ (-α))
    (hX : IsKLInput P X) :
    (∀ᵐ ω ∂P, Tendsto
      (fun κ : ℕ => l2S2Sq (fun y => klField A X ω y - klTrunc A X κ ω y))
      atTop (𝓝 0)) ∧
    ∀ β : ℝ, β < (α - 2) / 2 →
      ∀ᵐ ω ∂P, ∀ᶠ κ : ℕ in atTop,
        l2S2Sq (fun y => klField A X ω y - klTrunc A X κ ω y) ≤
          ENNReal.ofReal ((κ : ℝ) ^ (-β)) ^ (2 : ℕ) := by sorry

end SphereGRF.Truncation
