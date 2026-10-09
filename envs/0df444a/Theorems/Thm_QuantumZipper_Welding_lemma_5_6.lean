-- Prove2me | Theorems.Thm_QuantumZipper_Welding_lemma_5_6
-- name    : QuantumZipper.Welding.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:35.697698+00:00
-- url     : https://prove2.me/theorems/dee15ba3-7321-4761-914c-021a59807cdd
-- title:
--   Lemma 5.6 — sampling $x$ from $\nu_h[-\delta,0]$ under $\Gamma$ turns the zipper into $\mathrm{SLE}_{\kappa,\rho}$ with $\rho=\gamma^2\delta_x-\gamma^2\sigma_{0,1}$
-- statement:
--   Let $\kappa\in(0,4)$, $\gamma=\sqrt\kappa$ and $\delta\in(0,1)$. Sample $(h^t,\eta^t)$ from $\nu_h[-\delta,0]\,\Gamma$, normalized to a probability measure, with $h=h^0$ normalized by $h_1(0)=0$. Then sample $x$ from $\nu_h$ restricted to $[-\delta,0]$, normalized. Then:
--
--   1. given $x$, the zipping-up process $f_t$ has the law of the modified SLE process of Theorem 4.5 with
--   $$\rho=\gamma^2\delta_x-\gamma^2\sigma_{0,1},$$
--   where $\sigma_{0,1}$ is the uniform probability measure on the upper unit semicircle; the flow runs until $0\in f_t(\mathcal C_x)$, $\mathcal C_x=\{x\}\cup(\partial B_1(0)\cap\overline{\mathbb H})$;
--   2. given $f_t$ for some $t\ge0$ (and $x$), the conditional law of $h^0$ is that of $\tilde h\circ f_t+\hat{\mathfrak h}_t$, with $\hat{\mathfrak h}_t$ as in (4.4) for this $\rho$.
--
--   The lemma computes the law of the zipper started from a quantum-length-typical boundary point. This is the configuration of Figure 1.7 from which Theorem 1.8 is proved.
--
--   **Formalization Note** The joint law of $(\omega,x)$ is $Z^{-1}P(d\omega)\,\nu_\omega|_{[-\delta,0]}(dx)$. "The unit circle" is read as the upper semicircle $\partial B_1(0)\cap\mathbb H$, as the proof's (5.9) and (5.11) require. $\rho$ is the measure of (4.6) itself. Part 1 is stated through Lévy's characterization: with $B'_t=B_t-\frac1{\sqrt\kappa}\int_0^t\big(-\operatorname{Re}f_s^{-1},\rho\big)ds$, for every $\theta$ and every $\varepsilon>0$ the process $\exp\big(i\theta B'_{t\wedge\tau_\varepsilon}+\tfrac{\theta^2}2(t\wedge\tau_\varepsilon)\big)$ is a martingale for $\sigma(x)\vee\sigma(B_s:s\le t)$. Here $\tau_\varepsilon$ increases to the first time $0\in f_t(\mathcal C_x)$, which keeps the drift integrals absolutely convergent. Part 2 is the conditionally Gaussian law on $\{t<\tau_0\}$ given that filtration. $\nu$ is assumed measurable as a random measure.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Lemma 5.6, pp. 66–67 (with (5.9), p. 67, and (5.11), p. 69)

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting
import Definitions.Def_QuantumZipper_Welding_QuantumLength
import Definitions.Def_QuantumZipper_Welding_Zipper

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Welding

/-- **Lemma 5.6** (Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Lemma 5.6,
pp. 66–67). Let `κ ∈ (0, 4)`, `γ = √κ`, `δ ∈ (0, 1)`. Sample `(h^t, η^t)` from `ν_h[−δ, 0] Γ`
(normalized; `h = h⁰`) and then `x` from `ν_h` restricted to `[−δ, 0]` (normalized). Then given
`x`, the zipping-up process `f_t` is the modified SLE of Theorem 4.5 with
`ρ = γ² δ_x − γ² σ_{0,1}`; and given `f_t` (and `x`), the conditional law of `h⁰` is that of
`h̃ ∘ f_t + ĥ_t` ((4.4)).

**Formalization Note**
* `Γ` is `IsGammaZipper` (its restriction to `(h⁰, (f_t)_{t ≥ 0})`), with `h⁰₁(0) = 0` ((5.9),
  p. 67), which fixes the weight `ν_h[−δ, 0]`. `ν ω` is the quantum boundary length (1.2) of `h⁰`,
  assumed measurable in `ω` as a random measure.
* The joint law of `(ω, x)` is `Qx(dω, dx) = Z⁻¹ P(dω) ν_ω|_{[−δ,0]}(dx)`, which is the two-step
  sampling of the statement.
* **"The unit circle" is read as the upper unit semicircle `∂B₁(0) ∩ ℍ` with its uniform
  probability measure `σ_{0,1}`** (the proof uses `h₁(0)` and `∂B₁(0)`, (5.9), and (5.11) integrates
  `∫₀^π … dθ/π`); disclosed. `ρ` is the (4.6) measure itself (not rescaled by `2√κ`, cf. p. 68).
* The flow runs until `τ`, the first time `0 ∈ f_t(𝒞_x)` with `𝒞_x = {x} ∪` the closed upper unit
  semicircle (Theorem 4.5's stopping rule).
* First clause: with `B'_t = B_t − (1/√κ) ∫₀ᵗ (−Re f_s⁻¹, ρ_x) ds`, for every `θ ∈ ℝ` and every
  `ε > 0` the stopped process `exp(iθ B'_{t∧τ_ε} + θ²(t∧τ_ε)/2)` is a `Qx`-martingale for the
  filtration `𝒢_t = σ(x) ∨ σ(B_s : s ≤ t)`, where `τ_ε ↑ τ` is the first time `f_t(𝒞_x)` comes within
  `ε` of `0`. By Lévy's characterization this says that, given `x`, `B'` is a Brownian motion up to
  `τ`, i.e. that `W = √κ B' + ∫ (−Re f_s⁻¹, ρ_x) ds` is the driving function of (4.5)–(4.6) up to `τ`.
  The localization keeps every drift integral absolutely convergent (near `τ` the drift
  `−γ²/f_s(x)` need not be integrable when `κ ≤ 2`, (4.9), (5.12)).
* Second clause: for each `t`, on `{t < τ}` and given `𝒢_t`, the pairings of `h⁰` are Gaussian with
  the mean of `ĥ_t` ((4.4) for `ρ_x`) and the covariance of `h̃ ∘ f_t`. -/
theorem lemma_5_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ0 : 0 < κ) (hκ4 : κ < 4) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (B : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0 → ℂ → ℂ) (Ψ : Ω → Measure ℂ → ℝ)
    (hΓ : IsGammaZipper κ P B g Ψ)
    (ν : Ω → Measure ℝ) (hν_meas : Measurable ν)
    (hν : ∀ᵐ ω ∂P, IsBoundaryLengthOn (Real.sqrt κ) Set.univ
      (fun x ε => arcAvg (Ψ ω) (x : ℂ) ε) (ν ω)) :
    let γ : ℝ := Real.sqrt κ
    let Qx : Measure (Ω × ℝ) :=
      (∫⁻ ω, ν ω (Set.Icc (-δ) 0) ∂P)⁻¹ •
        P.bind (fun ω => ((ν ω).restrict (Set.Icc (-δ) 0)).map (fun x => (ω, x)))
    let ρp : ℝ → Measure ℂ := fun x => ENNReal.ofReal (γ ^ 2) • Measure.dirac (x : ℂ)
    let ρn : Measure ℂ := ENNReal.ofReal (γ ^ 2) • sigma01
    let τ : ℝ → Ω × ℝ → ℝ≥0∞ := fun ε p => hitTime (bmDrive κ B p.1) (g p.1) p.2 ε
    let stopAt : ℝ → ℝ≥0 → Ω × ℝ → ℝ≥0 := fun ε t p => (min (t : ℝ≥0∞) (τ ε p)).toNNReal
    let B' : ℝ≥0 → Ω × ℝ → ℝ := fun t p => B t p.1 - 1 / Real.sqrt κ *
      ∫ s in (0 : ℝ)..(t : ℝ), drift (bmDrive κ B p.1) (g p.1) (ρp p.2) ρn (Real.toNNReal s)
    let 𝒢 : ℝ≥0 → MeasurableSpace (Ω × ℝ) := fun t =>
      MeasurableSpace.comap Prod.snd inferInstance ⊔
        ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (fun p : Ω × ℝ => B s p.1) inferInstance
    (∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, ∀ s t : ℝ≥0, s ≤ t → ∀ S : Set (Ω × ℝ), MeasurableSet[𝒢 s] S →
      ∫ p in S, Complex.exp (Complex.I * ((θ * B' (stopAt ε t p) p : ℝ) : ℂ)
          + ((θ ^ 2 / 2 * (stopAt ε t p : ℝ) : ℝ) : ℂ)) ∂Qx =
        ∫ p in S, Complex.exp (Complex.I * ((θ * B' (stopAt ε s p) p : ℝ) : ℂ)
          + ((θ ^ 2 / 2 * (stopAt ε s p : ℝ) : ℝ) : ℂ)) ∂Qx) ∧
    ∀ t : ℝ≥0, IsCondGaussianFieldOn Qx (𝒢 t) {p | (t : ℝ≥0∞) < τ 0 p} IsAdmissible
      (fun p => Ψ p.1)
      (fun p μ => normMean (hatH κ (bmDrive κ B p.1) (g p.1) (ρp p.2) ρn t) μ)
      (fun p μ ν' => normCov (revCov (bmDrive κ B p.1) (g p.1) t) μ ν') := by sorry

end QuantumZipper.Welding
