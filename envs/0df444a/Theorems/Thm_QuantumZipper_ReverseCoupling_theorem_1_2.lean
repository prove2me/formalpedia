-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_theorem_1_2
-- name    : QuantumZipper.ReverseCoupling.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:33.651623+00:00
-- url     : https://prove2.me/theorems/39146579-8dc2-4e0e-8da1-778e2016cd0b
-- title:
--   Theorem 1.2, pp. 13–14 — zipping up by reverse SLE_κ preserves the law of 𝔥₀ + h̃: 𝔥_T + h̃∘f_T and 𝔥₀ + h̃ agree in law modulo additive constants
-- statement:
--   Fix $\kappa>0$ and a deterministic time $T>0$. Let $B$ be a standard Brownian motion and let $f_t$ be the reverse Loewner flow
--   $$df_t(z)=\frac{-2}{f_t(z)}\,dt-\sqrt\kappa\,dB_t,\qquad f_0(z)=z .\qquad(1.7)$$
--   Write
--   $$\mathfrak h_0(z)=\frac{2}{\sqrt\kappa}\log|z|,\qquad Q=\frac{2}{\sqrt\kappa}+\frac{\sqrt\kappa}{2},\qquad \mathfrak h_t(z)=\mathfrak h_0(f_t(z))+Q\log|f'_t(z)| ,$$
--   and let $\tilde h$ be a free boundary GFF on $\mathbb H$, independent of $B$. Then the two random distributions modulo additive constants
--   $$h=\mathfrak h_0+\tilde h\qquad\text{and}\qquad h\circ f_T+Q\log|f'_T|=\mathfrak h_T+\tilde h\circ f_T$$
--   agree in law: for every $n$ and every family $\rho_1,\dots,\rho_n$ of mean-zero test functions, the pairing vectors $\big((\mathfrak h_T+\tilde h\circ f_T,\rho_j)\big)_j$ and $\big((\mathfrak h_0+\tilde h,\rho_j)\big)_j$ have the same law.
--
--   Equivalently, the law of the quantum surface $(\mathbb H,h)$ is invariant under independently sampling $f_T$, cutting out the hull $K_T$ and changing coordinates by $f_T^{-1}$. This is the reverse coupling of SLE$_\kappa$ with the free boundary GFF on which the quantum gravity zipper is built.
--
--   **Formalization Note** Given $B$, the vector $((\mathfrak h_T+\tilde h\circ f_T,\rho_j))_j$ is Gaussian with mean $((\mathfrak h_T,\rho_j))_j$ and covariance $(E_T(\rho_i,\rho_j))_{i,j}$: by the pull-back convention of footnote 1 (p. 7), $(\tilde h\circ f_T,\rho)=(\tilde h,\rho^{f_T})$ with $\rho^{f_T}=|(f_T^{-1})'|^2\rho\circ f_T^{-1}$, a mean-zero test function, and $E(\rho_i^{f_T},\rho_j^{f_T})=E_T(\rho_i,\rho_j)$ by a change of variables. The Lean statement therefore says that the $P$-mixture of $\mathcal N\big(((\mathfrak h_T,\rho_j))_j,(E_T(\rho_i,\rho_j))\big)$, evaluated on any Borel set as a lower Lebesgue integral, equals the law of $\big((\mathfrak h_0,\rho_j)+(\tilde h,\rho_j)\big)_j$; independence is encoded by placing $\tilde h$ on its own probability space. $B$ is a Brownian motion with every path continuous and every coordinate measurable, and the flow is required for every path. $\kappa>0$ is arbitrary; the hull $K_T$ does not enter.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Theorem 1.2, pp. 13–14, (1.7); footnote 1, p. 7; footnote 7, p. 14

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **Theorem 1.2** (reverse SLE$_κ$/GFF coupling). Sheffield, Conformal weldings of random surfaces,
arXiv:1012.4797v2, Theorem 1.2, pp. 13–14.

Fix `κ > 0` and a deterministic time `T > 0`. Let `B` be a standard Brownian motion on `(Ω, P)`,
`f_t = g_t − √κ B_t` the reverse Loewner flow (1.7), `𝔥₀ = (2/√κ) log |·|`,
`𝔥_T = 𝔥₀ ∘ f_T + Q log |f′_T|`, and let `h̃` be a free boundary GFF on `ℍ` independent of `B`.
Then `h = 𝔥₀ + h̃` and `𝔥_T + h̃ ∘ f_T` agree in law as random distributions modulo additive
constants: for every finite family `ρ₁, …, ρₙ` of mean-zero test functions the two pairing vectors
have the same law.

**Formalization Note** (encoding through the conditional law given `B`).
* `h̃` lives on its own probability space `(Ω', P')`; independence from `B` is encoded by
  mixing over `P`. Given `B`, the vector `((𝔥_T + h̃ ∘ f_T, ρ_j))_j` is Gaussian with mean
  `((𝔥_T, ρ_j))_j` and covariance `(E_T(ρ_i, ρ_j))_{ij}`: by the pull-back convention of footnote 1
  (p. 7), `(h̃ ∘ f_T, ρ) = (h̃, ρ^{f_T})` with `ρ^{f_T} = |(f_T⁻¹)′|² ρ ∘ f_T⁻¹`, again a mean-zero
  test function on `ℍ`, and a change of variables gives `E(ρ_i^{f_T}, ρ_j^{f_T}) = E_T(ρ_i, ρ_j)`.
  This identification is a disclosed reading, not an item. The left side below is therefore
  `P(ω ↦ N(m_T(ω), Σ_T(ω)))`-mixture evaluated on a Borel set `A`, written as a lower Lebesgue
  integral (no measurability of the kernel is assumed, so no junk value can arise).
* The right side is the law of `(((𝔥₀, ρ_j) + (h̃, ρ_j)))_j` under `P'`.
* `B` is taken with every path continuous and every coordinate measurable (a version of Brownian
  motion, cf. the discussion on p. 42), and the flow is required for every sample path.
* `T` is fixed and deterministic; `κ > 0` is arbitrary (no `κ < 4`). The hull `K_T` does not enter. -/
theorem theorem_1_2 (κ : ℝ) (hκ : 0 < κ) (T : ℝ≥0) (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (g : Ω → ℝ≥0 → ℂ → ℂ) (hg : ∀ ω, IsReverseLoewnerFlow (drive κ B ω) (g ω))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (htilde : Ω' → TestFn → ℝ) (hGFF : IsFreeBoundaryGFF htilde P')
    (n : ℕ) (ρ : Fin n → TestFn) (hρ : ∀ j, MeanZero (ρ j))
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A) :
    ∫⁻ ω, multivariateGaussian
        (pairVec fun j => pairing (frakH κ (drive κ B ω) (g ω) T) (ρ j))
        (Matrix.of fun i j => Et (drive κ B ω) (g ω) T (ρ i) (ρ j)) A ∂P =
      P'.map (fun ω' => pairVec fun j => pairing (frakH0 κ) (ρ j) + htilde ω' (ρ j)) A := by sorry

end QuantumZipper.ReverseCoupling
