-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_frakH_point_martingale
-- name    : QuantumZipper.ReverseCoupling.frakH_point_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:17.179223+00:00
-- url     : https://prove2.me/theorems/e10cecc4-5cc9-4d33-97a3-25f93d65811b
-- title:
--   §4.1, p. 48 — for fixed z ∈ ℍ, 𝔥_t(z) is a martingale (reverse flow)
-- statement:
--   Let $\kappa>0$, let $B$ be a standard Brownian motion, and let $f_t$ be the reverse Loewner flow driven by $W_t=\sqrt\kappa B_t$. For each fixed $z\in\mathbb H$, the process
--   $$\mathfrak h_t(z)=\frac{2}{\sqrt\kappa}\log|f_t(z)|+Q\log|f'_t(z)|,\qquad t\ge0,$$
--   is a martingale with respect to the natural filtration of $B$ (a true martingale, not merely a local martingale).
--
--   It is the pointwise version of the martingale $(\mathfrak h_t,\rho)$ that drives the proof of Theorem 1.2.
--
--   **Formalization Note** $B$ is a Brownian motion in Mathlib's sense (`IsBrownianReal`) with every path continuous and every coordinate measurable; the flow is required for every path. The martingale property includes adaptedness and holds for all $t\ge0$.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 48 (reverse case)

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **§4.1, p. 48** (unnumbered): "This immediately implies that `𝔥_t(z)` is a martingale (not merely a
local martingale) because for each `z` and `t`, `𝔥_t(z)` represents the value of a Brownian motion
stopped at a random time that is strictly less than a constant times `t`."
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 48 (reverse case).

For `κ > 0` and each fixed `z ∈ ℍ`, the process `t ↦ 𝔥_t(z) = 𝔥₀(f_t(z)) + Q log |f′_t(z)|` is a
martingale for the reverse Loewner flow driven by `√κ B`.

**Formalization Note** `B` is a standard Brownian motion (`IsBrownianReal`) with every path
continuous and every coordinate measurable, `W = √κ B`, and the reverse Loewner flow is required
for every sample path. The martingale property is with respect to the natural filtration
`σ(B_s : s ≤ t)` and holds for all times `t ≥ 0` (Mathlib's `Martingale` includes adaptedness and
the conditional-expectation identity; integrability is part of its content). -/
theorem frakH_point_martingale (κ : ℝ) (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (g : Ω → ℝ≥0 → ℂ → ℂ) (hg : ∀ ω, IsReverseLoewnerFlow (drive κ B ω) (g ω))
    (z : ℂ) (hz : 0 < z.im) :
    Martingale (fun t ω => frakH κ (drive κ B ω) (g ω) t z) (brownianFiltration B hBm) P := by sorry

end QuantumZipper.ReverseCoupling
