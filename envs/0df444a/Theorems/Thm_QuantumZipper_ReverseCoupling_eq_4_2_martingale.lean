-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_eq_4_2_martingale
-- name    : QuantumZipper.ReverseCoupling.eq_4_2_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:44.602515+00:00
-- url     : https://prove2.me/theorems/925e1c1d-a9d3-43bb-b028-b4cf7e69bdbe
-- title:
--   §4.1, (4.2), pp. 49–50 — (𝔥_t,ρ₁)(𝔥_t,ρ₂) + E_t(ρ₁,ρ₂) is a martingale
-- statement:
--   Let $\kappa>0$, $B$ a standard Brownian motion, and $f_t$ the reverse Loewner flow driven by $\sqrt\kappa B$. For mean-zero test functions $\rho_1,\rho_2$ on $\mathbb H$, the process
--   $$(\mathfrak h_t,\rho_1)(\mathfrak h_t,\rho_2)+\int_{\mathbb H}\int_{\mathbb H}\rho_1(x)\,\rho_2(y)\,G_t(x,y)\,dx\,dy\qquad(4.2)$$
--   is a martingale with respect to the natural filtration of $B$.
--
--   This identifies the cross variation $d\langle(\mathfrak h_t,\rho_1),(\mathfrak h_t,\rho_2)\rangle=-dE_t(\rho_1,\rho_2)$, so $(\mathfrak h_t,\rho)$ is a Brownian motion when parameterized by $-E_t(\rho)$.
--
--   **Formalization Note** The martingale form is the paper's own characterization of the cross variation (p. 49); no quadratic variation is formalized.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, (4.2), pp. 49–50 (reverse case)

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **§4.1, (4.2), pp. 49–50**: "Thus it suffices for us to show that
`(𝔥_t, ρ₁)(𝔥_t, ρ₂) + ∫ ρ₁(x) ρ₂(y) G_t(x, y) dx dy` (4.2) is a martingale." — and p. 50: "we can
use Fubini's theorem to conclude that (4.2) is a martingale."
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, (4.2), pp. 49–50 (reverse case).

For `κ > 0` and mean-zero test functions `ρ₁, ρ₂` on `ℍ`, the process
`t ↦ (𝔥_t, ρ₁)(𝔥_t, ρ₂) + E_t(ρ₁, ρ₂)`, `E_t(ρ₁, ρ₂) = ∫∫ ρ₁(x) G_t(x, y) ρ₂(y) dx dy`, is a martingale.

**Formalization Note** `B` is a standard Brownian motion (`IsBrownianReal`) with every path
continuous and every coordinate measurable, `W = √κ B`, and the reverse Loewner flow is required
for every sample path. The martingale property is with respect to the natural filtration
`σ(B_s : s ≤ t)` and holds for all times `t ≥ 0` (Mathlib's `Martingale` includes adaptedness and
the conditional-expectation identity; integrability is part of its content). This martingale statement is the paper's own characterization (p. 49) of the cross
variation `d⟨(𝔥_t, ρ₁), (𝔥_t, ρ₂)⟩ = −dE_t(ρ₁, ρ₂)` of the table on p. 47; no quadratic variation is
formalized. -/
theorem eq_4_2_martingale (κ : ℝ) (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (g : Ω → ℝ≥0 → ℂ → ℂ) (hg : ∀ ω, IsReverseLoewnerFlow (drive κ B ω) (g ω))
    (ρ₁ ρ₂ : TestFn) (hρ₁ : MeanZero ρ₁) (hρ₂ : MeanZero ρ₂) :
    Martingale (fun t ω => pairing (frakH κ (drive κ B ω) (g ω) t) ρ₁ *
        pairing (frakH κ (drive κ B ω) (g ω) t) ρ₂ + Et (drive κ B ω) (g ω) t ρ₁ ρ₂)
      (brownianFiltration B hBm) P := by sorry

end QuantumZipper.ReverseCoupling
