-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_one_dim_law
-- name    : QuantumZipper.ReverseCoupling.one_dim_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:29.923469+00:00
-- url     : https://prove2.me/theorems/751cff09-ea4e-476e-82f6-256364a410cb
-- title:
--   §4.1, p. 50 — (𝔥_T + h̃∘f_T, ρ) has the law N((𝔥₀,ρ), E₀(ρ))
-- statement:
--   Let $\kappa>0$, $T>0$, $B$ a standard Brownian motion and $f_t$ the reverse Loewner flow driven by $\sqrt\kappa B$. Let $\rho$ be a mean-zero test function on $\mathbb H$. Given $B$, the pairing $(\mathfrak h_T+\tilde h\circ f_T,\rho)$ with an independent free boundary GFF $\tilde h$ is Gaussian with mean $(\mathfrak h_T,\rho)$ and variance $E_T(\rho)$. Its unconditional law is
--   $$\mathbb E\Big[\mathcal N\big((\mathfrak h_T,\rho),\,E_T(\rho)\big)\Big]=\mathcal N\big((\mathfrak h_0,\rho),\,E_0(\rho)\big),$$
--   that is, for every Borel set $A\subseteq\mathbb R$, $\mathbb E\big[\mathcal N((\mathfrak h_T,\rho),E_T(\rho))(A)\big]=\mathcal N((\mathfrak h_0,\rho),E_0(\rho))(A)$, where $E_0(\rho)=E(\rho,\rho)$.
--
--   This is the one-dimensional case of Theorem 1.2; with Proposition 3.1 it yields the full statement.
--
--   **Formalization Note** The conditional law given $B$ is written directly as `gaussianReal`, with variances passed through `Real.toNNReal` (both are nonnegative for mean-zero $\rho$). The reading $(\tilde h\circ f_T,\rho)=(\tilde h,\rho^{f_T})$ with $E(\rho^{f_T})=E_T(\rho)$ (footnote 1, p. 7, and a change of variables) is disclosed, not formalized. The expectation is a lower Lebesgue integral, so no measurability of the kernel is assumed.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 50; Figure 4.1, p. 49

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **§4.1, p. 50** (unnumbered): "… since each `(𝔥_T + h̃ ∘ f_T, ρ)` is a sum of a standard Brownian
motion stopped at time `E₀(ρ) − E_T(ρ)` and a conditionally independent Gaussian of variance `E_T(ρ)`,
it has the same law as a Gaussian of variance `E₀(ρ)` and mean `(𝔥₀, ρ)`."
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 50 (reverse case).

For `κ > 0`, a fixed time `T > 0` and a mean-zero test function `ρ`, mixing the Gaussian law
`N((𝔥_T, ρ), E_T(ρ))` over the Brownian path gives `N((𝔥₀, ρ), E₀(ρ))`:
for every Borel `A ⊆ ℝ`, `E[N((𝔥_T, ρ), E_T(ρ))(A)] = N((𝔥₀, ρ), E₀(ρ))(A)`.

**Formalization Note** `B` is a standard Brownian motion (`IsBrownianReal`) with every path
continuous and every coordinate measurable, `W = √κ B`, and the reverse Loewner flow is required
for every sample path. The martingale property is with respect to the natural filtration
`σ(B_s : s ≤ t)` and holds for all times `t ≥ 0` (Mathlib's `Martingale` includes adaptedness and
the conditional-expectation identity; integrability is part of its content). `N((𝔥_T, ρ), E_T(ρ))` is the conditional law of `(𝔥_T + h̃ ∘ f_T, ρ)` given `B` (footnote 1,
p. 7, and `E(ρ^{f_T}) = E_T(ρ)`, a disclosed reading). `E₀(ρ)` is `E(ρ, ρ)` of (3.6) (`f₀ = id`).
Variances are passed to `gaussianReal` through `Real.toNNReal`; both are nonnegative for mean-zero
`ρ`. The mixture is a lower Lebesgue integral, so no measurability of the kernel is assumed. -/
theorem one_dim_law (κ : ℝ) (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (g : Ω → ℝ≥0 → ℂ → ℂ) (hg : ∀ ω, IsReverseLoewnerFlow (drive κ B ω) (g ω))
    (T : ℝ≥0) (hT : 0 < T) (ρ : TestFn) (hρ : MeanZero ρ) (A : Set ℝ) (hA : MeasurableSet A) :
    ∫⁻ ω, gaussianReal (pairing (frakH κ (drive κ B ω) (g ω) T) ρ)
        (Real.toNNReal (Et (drive κ B ω) (g ω) T ρ ρ)) A ∂P =
      gaussianReal (pairing (frakH0 κ) ρ) (Real.toNNReal (energy ρ ρ)) A := by sorry

end QuantumZipper.ReverseCoupling
