-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_product_green_martingale
-- name    : QuantumZipper.ReverseCoupling.product_green_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:25.538013+00:00
-- url     : https://prove2.me/theorems/5d5c5303-8c00-45a9-b7ec-8ea9a632f672
-- title:
--   §4.1, p. 50 — 𝔥_t(x)𝔥_t(y) + G_t(x,y) is a martingale for fixed x ≠ y in ℍ
-- statement:
--   Let $\kappa>0$, $B$ a standard Brownian motion, and $f_t$ the reverse Loewner flow driven by $\sqrt\kappa B$. For fixed $x\neq y$ in $\mathbb H$, the process
--   $$\mathfrak h_t(x)\,\mathfrak h_t(y)+G_t(x,y),\qquad G_t(x,y)=G(f_t(x),f_t(y)),$$
--   is a martingale with respect to the natural filtration of $B$.
--
--   Integrating against $\rho_1(x)\rho_2(y)$ yields the martingale (4.2).
--
--   **Formalization Note** $x\neq y$ is implicit on the page. The following sentence of the paper ("$G_t(x,y)$ is non-increasing") holds for the forward flow, not pointwise for the reverse flow, and is not stated.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 50 (reverse case)

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **§4.1, p. 50** (unnumbered): "We know from the above calculations that
`𝔥_t(x)𝔥_t(y) + G_t(x, y)` is a martingale for fixed `x` and `y` in `ℍ`."
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 50 (reverse case).

For `κ > 0` and fixed `x ≠ y` in `ℍ`, `t ↦ 𝔥_t(x)𝔥_t(y) + G_t(x, y)` is a martingale, where
`G_t(x, y) = G^{ℍ_F}(f_t(x), f_t(y))`.

**Formalization Note** `B` is a standard Brownian motion (`IsBrownianReal`) with every path
continuous and every coordinate measurable, `W = √κ B`, and the reverse Loewner flow is required
for every sample path. The martingale property is with respect to the natural filtration
`σ(B_s : s ≤ t)` and holds for all times `t ≥ 0` (Mathlib's `Martingale` includes adaptedness and
the conditional-expectation identity; integrability is part of its content). `x ≠ y` is implicit (`G` is singular on the diagonal). The next sentence of the page
("`G_t(x, y)` is non-increasing") is a forward-flow fact and is not stated. -/
theorem product_green_martingale (κ : ℝ) (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (g : Ω → ℝ≥0 → ℂ → ℂ) (hg : ∀ ω, IsReverseLoewnerFlow (drive κ B ω) (g ω))
    (x y : ℂ) (hx : 0 < x.im) (hy : 0 < y.im) (hxy : x ≠ y) :
    Martingale (fun t ω => frakH κ (drive κ B ω) (g ω) t x * frakH κ (drive κ B ω) (g ω) t y +
      Gt (drive κ B ω) (g ω) t x y) (brownianFiltration B hBm) P := by sorry

end QuantumZipper.ReverseCoupling
