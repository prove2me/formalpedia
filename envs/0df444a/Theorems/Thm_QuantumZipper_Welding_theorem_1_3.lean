-- Prove2me | Theorems.Thm_QuantumZipper_Welding_theorem_1_3
-- name    : QuantumZipper.Welding.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:00.941135+00:00
-- url     : https://prove2.me/theorems/29fc70a5-4ee6-4f9b-b8c3-984f8a285bf6
-- title:
--   Theorem 1.3 — for $\kappa<4$ reverse $\mathrm{SLE}_\kappa$ zipping welds boundary arcs of equal quantum length, $\nu_h[z_-,0]=\nu_h[0,z_+]$
-- statement:
--   Let $\kappa\in(0,4)$, $\gamma=\sqrt\kappa$ and $T>0$. Sample a standard Brownian motion $B$, and let $f_t$ be the reverse Loewner flow
--   $$df_t(z)=\frac{-2}{f_t(z)}\,dt-\sqrt\kappa\,dB_t,\qquad f_0(z)=z,$$
--   up to time $T$. The curve is $\eta_T((0,T])=\mathbb H\setminus f_T(\mathbb H)$. Independently of $B$, let $\tilde h$ be a free boundary GFF, and set
--   $$h=\mathfrak h_T+\tilde h\circ f_T,\qquad\mathfrak h_T(z)=\tfrac2{\sqrt\kappa}\log|f_T(z)|+Q\log|f_T'(z)|,\quad Q=\tfrac2{\sqrt\kappa}+\tfrac{\sqrt\kappa}2 .$$
--   Let $\nu_h$ be the quantum boundary length (1.2). For a point $z$ on $\eta_T$, let $z_-<0<z_+$ be the two real points that $f_T$, continuously extended to $\mathbb R$, maps to $z$. Then almost surely
--   $$\nu_h\big([z_-,0]\big)=\nu_h\big([0,z_+]\big)\qquad\text{for all }z\text{ on }\eta_T.$$
--
--   The reverse Loewner flow thus performs a conformal welding: it glues the boundary interval $[z_-,0]$ to $[0,z_+]$ by quantum length. With the removability of $\mathrm{SLE}_\kappa$ curves for $\kappa<4$, this implies that the field $h$ determines the curve $\eta_T$ (Theorem 1.4).
--
--   **Formalization Note** The additive constant is fixed by $h_1(0)=0$; the conclusion does not depend on it. The field enters through its arc averages. Given $B$, these are Gaussian with mean from $\mathfrak h_T$ and covariance $\iint G(f_Tu,f_Tv)$ against the normalized arc measures; this is the law of $\mathfrak h_T+\tilde h\circ f_T$ with $\tilde h$ independent of $B$. The continuous version of the arc averages is used, and $\nu_h$ is any measure satisfying the defining limit. The points $z_\pm$ are encoded by radial boundary limits $f_T(z_\pm+iy)\to z$ as $y\downarrow0$; the continuous extension is not assumed.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Theorem 1.3, pp. 15–16 (setting of Theorem 1.2, pp. 13–14; normalization p. 15)

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting
import Definitions.Def_QuantumZipper_Welding_QuantumLength

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Welding

/-- **Theorem 1.3** (Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2,
Theorem 1.3, pp. 15–16). Let `κ ∈ (0, 4)`, `γ = √κ`, `T > 0`. Sample a standard Brownian motion `B`,
let `f_t = g_t − √κ B_t` be the reverse Loewner flow (1.7), and let `h = 𝔥_T + h̃ ∘ f_T` with `h̃`
a free boundary GFF independent of `B`, the additive constant fixed by `h₁(0) = 0`. Let `ν_h` be the
quantum boundary length (1.2). Then almost surely, for every `z ∈ η_T((0, T]) = ℍ \ f_T(ℍ)` and every
pair `z₋ < 0 < z₊` of real points that `f_T` (continuously extended to `ℝ`) maps to `z`,
`ν_h([z₋, 0]) = ν_h([0, z₊])`.

**Formalization Note**
* The field `h` enters only through its arc averages: `Ψ ω μ = (h, μ − μ(ℂ)σ_{0,1})`. The hypothesis
  `hΨ` says that conditionally on `B` these are Gaussian with mean `∫ 𝔥_T d(μ − μ(ℂ)σ_{0,1})` and
  covariance `∫∫ G(f_T u, f_T v)` against the same normalized measures, which is the law of
  `𝔥_T + h̃ ∘ f_T` for `h̃` independent of `B` (footnote 1, p. 7, and (3.6) extended to measures,
  §3.3, p. 41). `hΨ_reg` selects the continuous version of `(x, ε) ↦ h_ε(x)` ([DS11a], cited p. 41),
  from which `ν` is built.
* The normalization `h₁(0) = 0` is the paper's own (Figure 1.7, (5.9)); the conclusion does not
  depend on the additive constant (p. 15: "The choice does not affect the theorem statement").
* `ν` is any measure satisfying `IsBoundaryLengthOn` (it is unique; its a.s. existence is [DS11a]).
* "The two points `z₋ < 0 < z₊` that `f_T` maps to `z`" is encoded by radial boundary limits
  `f_T(z_± + iy) → z` as `y ↓ 0`; the continuous extension of `f_T` to `ℝ` ([RS05]) is not assumed. -/
theorem theorem_1_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ0 : 0 < κ) (hκ4 : κ < 4) (T : ℝ≥0) (hT : 0 < T)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (g : Ω → ℝ≥0 → ℂ → ℂ)
    (hg : ∀ᵐ ω ∂P, QuantumZipper.ReverseCoupling.IsReverseLoewnerFlow (bmDrive κ B ω) (g ω))
    (hg_meas : ∀ (t : ℝ≥0) (z : ℂ), Measurable fun ω => g ω t z)
    (Ψ : Ω → Measure ℂ → ℝ)
    (hΨ_reg : ∀ᵐ ω ∂P, IsRegularArcField (Ψ ω))
    (hΨ : IsCondGaussianFieldOn P (pathSigma B) Set.univ IsAdmissible Ψ
      (fun ω μ => normMean (frakH κ (bmDrive κ B ω) (g ω) T) μ)
      (fun ω μ ν => normCov (revCov (bmDrive κ B ω) (g ω) T) μ ν))
    (ν : Ω → Measure ℝ)
    (hν : ∀ᵐ ω ∂P, IsBoundaryLengthOn (Real.sqrt κ) Set.univ
      (fun x ε => arcAvg (Ψ ω) (x : ℂ) ε) (ν ω)) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, z ∈ Hplane → z ∉ (QuantumZipper.ReverseCoupling.revF (bmDrive κ B ω) (g ω) T) '' Hplane →
      ∀ zm zp : ℝ, zm < 0 → 0 < zp →
        Tendsto (fun y : ℝ => QuantumZipper.ReverseCoupling.revF (bmDrive κ B ω) (g ω) T ((zm : ℂ) + (y : ℂ) * Complex.I))
          (𝓝[>] 0) (𝓝 z) →
        Tendsto (fun y : ℝ => QuantumZipper.ReverseCoupling.revF (bmDrive κ B ω) (g ω) T ((zp : ℂ) + (y : ℂ) * Complex.I))
          (𝓝[>] 0) (𝓝 z) →
        ν ω (Set.Icc zm 0) = ν ω (Set.Icc 0 zp) := by sorry

end QuantumZipper.Welding
