-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_frakH_pair_martingale
-- name    : QuantumZipper.ReverseCoupling.frakH_pair_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:16.122008+00:00
-- url     : https://prove2.me/theorems/f9df468f-5b80-451d-81a6-dc8b7608040f
-- title:
--   §4.1, p. 48 — for mean-zero ρ, (𝔥_t, ρ) is a martingale (reverse flow)
-- statement:
--   Let $\kappa>0$, $B$ a standard Brownian motion, and $f_t$ the reverse Loewner flow driven by $\sqrt\kappa B$. For every smooth compactly supported $\rho$ on $\mathbb H$ with $\int_{\mathbb H}\rho=0$, the process
--   $$(\mathfrak h_t,\rho)=\int_{\mathbb H}\mathfrak h_t(z)\,\rho(z)\,dz,\qquad t\ge0,$$
--   is a martingale with respect to the natural filtration of $B$.
--
--   These are the martingales which, after the time change by $-E_t(\rho)$, become Brownian motions, as in Figure 4.1.
--
--   **Formalization Note** Same conventions for $B$ as in the pointwise statement. The page says "in both cases"; only the reverse case belongs to this mission. The mean-zero assumption is the one the paper makes for the reverse case (p. 47).
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 48 (reverse case)

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **§4.1, p. 48** (unnumbered): "In both cases, we also see that (for any fixed `t`), `𝔥_t(z)` is an
`L¹` function of `z` and the probability space, which allows us to use Fubini's theorem and conclude
that the `(𝔥_t, ρ)` are martingales."
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 48 (reverse case).

For `κ > 0` and every smooth compactly supported `ρ` on `ℍ` with mean zero, the process
`t ↦ (𝔥_t, ρ) = ∫_ℍ 𝔥_t(z) ρ(z) dz` is a martingale for the reverse Loewner flow driven by `√κ B`.

**Formalization Note** `B` is a standard Brownian motion (`IsBrownianReal`) with every path
continuous and every coordinate measurable, `W = √κ B`, and the reverse Loewner flow is required
for every sample path. The martingale property is with respect to the natural filtration
`σ(B_s : s ≤ t)` and holds for all times `t ≥ 0` (Mathlib's `Martingale` includes adaptedness and
the conditional-expectation identity; integrability is part of its content). "In both cases" also covers the forward flow of Theorem 1.1, which is not part of this mission;
only the reverse case is stated. `ρ` has mean zero as assumed on p. 47 for the reverse case. -/
theorem frakH_pair_martingale (κ : ℝ) (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (g : Ω → ℝ≥0 → ℂ → ℂ) (hg : ∀ ω, IsReverseLoewnerFlow (drive κ B ω) (g ω))
    (ρ : TestFn) (hρ : MeanZero ρ) :
    Martingale (fun t ω => pairing (frakH κ (drive κ B ω) (g ω) t) ρ) (brownianFiltration B hBm) P := by sorry

end QuantumZipper.ReverseCoupling
