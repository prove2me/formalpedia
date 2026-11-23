-- Prove2me | Theorems.Thm_StarShapedRisk_Representation_Supplement_theorem3_inf_convolution
-- name    : StarShapedRisk.Representation.Supplement.theorem3_inf_convolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:43:49.780899+00:00
-- url     : https://prove2.me/theorems/fe7fe0d3-712d-426f-9e6d-0b3f4c2c734a
-- title:
--   Theorem 3 (inf-convolution) — selection envelope and conditional attainment
-- statement:
--   Let $n>0$ and $\rho_i$ be star-shaped risk measures on $\mathcal X$ with attained convex envelopes $\rho_i=\min_{\gamma_i\in\Gamma_i}\gamma_i$. Assume condition (10): $\sum_i\rho_i(Z_i)\ge0$ whenever $\sum_i Z_i=0$. Write $\rho_\square$ for their inf-convolution. Then
--   $$\rho_\square(X)=\inf_{\delta\in\square_i\Gamma_i}\delta(X)\qquad(X\in\mathcal X),$$
--   where $\square_i\Gamma_i$ consists of all inf-convolutions of selections $\gamma_i\in\Gamma_i$. If an allocation $\sum_iY_i=X$ attains $\rho_\square(X)=\sum_i\rho_i(Y_i)$, the infimum over selection inf-convolutions is attained. This includes the final attainment clause of Theorem 3; no extra normality assumption is imposed on selections.
--
--   Differences from the source:
--   - encoding: min and inf in (13)–(16) → IsLeast for attained minima and IsGLB for infima; reason: retain attainment and exclude default values of real extrema
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2644, Theorem 3 (inf-convolution)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_Supplement_SelectionEnvelopes

namespace StarShapedRisk.Representation.Supplement

theorem theorem3_inf_convolution {Ω : Type*} (𝒳 : PositionSpace Ω)
    {n : ℕ} (hn : 0 < n) (ρ : Fin n → 𝒳.carrier → ℝ)
    (Γ : Fin n → Set (𝒳.carrier → ℝ))
    (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i))
    (hΓ : ∀ i, ∀ γ ∈ Γ i, IsConvexRiskMeasure 𝒳 γ)
    (hmin : ∀ i X, IsLeast {r : ℝ | ∃ γ ∈ Γ i, r = γ X} (ρ i X))
    (hnormal : NormalityCondition 𝒳 ρ) :
    ∀ X, IsGLB {r : ℝ | ∃ δ ∈ infConvolutionSelections 𝒳 Γ, r = δ X}
        (infConvolution 𝒳 ρ X) ∧
      ((∃ Y : Fin n → 𝒳.carrier, ∑ i, Y i = X ∧
          ∑ i, ρ i (Y i) = infConvolution 𝒳 ρ X) →
        IsLeast {r : ℝ | ∃ δ ∈ infConvolutionSelections 𝒳 Γ, r = δ X}
          (infConvolution 𝒳 ρ X)) := by sorry

end StarShapedRisk.Representation.Supplement
