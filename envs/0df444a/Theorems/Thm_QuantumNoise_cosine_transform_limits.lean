-- Prove2me | Theorems.Thm_QuantumNoise_cosine_transform_limits
-- name    : QuantumNoise.cosine_transform_limits
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:54.198364+00:00
-- url     : https://prove2.me/theorems/bbc0a930-469b-4b69-a416-41e09d5ec635
-- title:
--   Eqs. (4.15a)–(4.15c) — long-time limits of the cosine transforms
-- statement:
--   Let $(\hat I,\hat F)$ be a detector, $\hbar>0$, $\omega\neq0$ and $\delta\in\mathbb R$, and let $\hat A=\sqrt{2/T}\int_{-T/2}^{T/2}dt\cos(\omega t+\delta)\hat I(t)$, $\hat B=\sqrt{2/T}\int_{-T/2}^{T/2}dt\cos(\omega t)\hat F(t)$ (4.14). As $T\to\infty$:
--
--   1. $(\Delta A)^2\to\bar S_{II}[\omega]$ and $(\Delta B)^2\to\bar S_{FF}[\omega]$;
--   2. $\langle\{\hat A,\hat B\}\rangle\to 2\operatorname{Re}\,e^{i\delta}\bar S_{IF}[\omega]$;
--   3. $\langle[\hat A,\hat B]\rangle\to\displaystyle\int_{-\infty}^{+\infty}dt\cos(\omega t+\delta)\big\langle[\hat I(t),\hat F(0)]\big\rangle$, and
--   $$
--   \int_{-\infty}^{+\infty}dt\cos(\omega t+\delta)\big\langle[\hat I(t),\hat F(0)]\big\rangle=i\hbar\operatorname{Re}\Big[e^{i\delta}\big(\chi_{IF}[\omega]-(\chi_{FI}[\omega])^\ast\big)\Big].
--   $$
--
--   These are the frequency-resolved variances and correlators to which the uncertainty relation (4.13) is applied.
--
--   **Formalization Note** The second moments of $\hat A,\hat B$ are the double integrals `cosPairing` of correlators; "in the limit $T\to\infty$" is convergence as $T\to+\infty$. The last identity is exact and is stated separately.
--
--   Differences from the source:
--   - encoding: operators Â, B̂ (4.14) and their moments (ΔA)², ⟨{Â,B̂}⟩, ⟨[Â,B̂]⟩ → the double integrals cosPairing of the correlators ⟨a(t)b(s)⟩₀, whose sums and differences give the four moments; reason: the moments of the operator integrals are these integrals by linearity of the state; the operators themselves are not elements of an abstract ∗-algebra
--   - generalization: a detector with Hamiltonian Ĥdet and density matrix ρ̂0, Heisenberg operators Î(t), F̂(t) (p.21) → any unital ∗-algebra over ℂ, any one-parameter group τ of ∗-automorphisms, any τ-invariant state ρ₀ (StationaryDynamics); reason: Heisenberg evolution of a stationary density matrix is such a system; the general form also admits unbounded observables such as the cavity photon number F̂ = n̂ of Sec. III.B
--   - encoding: no regularity stated for the correlators ⟨a(t)b(0)⟩₀ → the correlators ⟨a(t)b⟩₀, a, b ∈ {Î, F̂}, are continuous and integrable on ℝ (fields of Detector); reason: the spectral densities (4.4), (4.7) and gains (4.3), (4.6), (5.49) are Fourier integrals of these correlators and are numbers only when they are integrable; otherwise Lean's integral is 0
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.3, Eqs. (4.14)–(4.15c), p.23

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chiTilde
import Definitions.Def_QuantumNoise_cosPairing

open Filter Topology

namespace QuantumNoise

/-- **Eqs. (4.15a)–(4.15c)** (Clerk et al., arXiv:0810.4729v2, Sec. IV.A.3, p.23; printed p.23 =
PDF p.23). Let `Â = √(2/T) ∫_{−T/2}^{T/2} dt cos(ωt + δ) Î(t)` and
`B̂ = √(2/T) ∫_{−T/2}^{T/2} dt cos(ωt) F̂(t)` (4.14). In the limit `T → ∞`, at any frequency
`ω ≠ 0` and for every phase `δ`:
`(ΔA)² → S̄II[ω]`, `(ΔB)² → S̄FF[ω]`, `⟨{Â, B̂}⟩ → 2 Re e^{iδ} S̄IF[ω]`, and
`⟨[Â, B̂]⟩ → ∫_{−∞}^{+∞} dt cos(ωt + δ) ⟨[Î(t), F̂(0)]⟩ = iħ Re[e^{iδ}(χIF[ω] − (χFI[ω])*)]`.

**Formalization Note** The second moments of `Â`, `B̂` are the double integrals `cosPairing`
(`⟨ÂÂ⟩ = cosPairing I I ω δ δ T`, `⟨B̂B̂⟩ = cosPairing F F ω 0 0 T`, `⟨ÂB̂⟩ = cosPairing I F ω δ 0 T`,
`⟨B̂Â⟩ = cosPairing F I ω 0 δ T`); the paper's "in the limit `T → ∞` we find" is
`Tendsto … atTop`. The last equality of (4.15c) is exact and is the fifth conjunct.
`χIF − (χFI)*` is `chiTilde`. -/
theorem cosine_transform_limits {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    [StarModule ℂ 𝒜] (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (hħ : 0 < ħ)
    (ω : ℝ) (hω : ω ≠ 0) (δ : ℝ) :
    Tendsto (fun T => cosPairing P D.I D.I ω δ δ T) atTop (𝓝 (Sbar P D.I D.I ω)) ∧
      Tendsto (fun T => cosPairing P D.F D.F ω 0 0 T) atTop (𝓝 (Sbar P D.F D.F ω)) ∧
      Tendsto (fun T => cosPairing P D.I D.F ω δ 0 T + cosPairing P D.F D.I ω 0 δ T) atTop
        (𝓝 (((2 * (Complex.exp ((δ : ℂ) * Complex.I) * Sbar P D.I D.F ω).re : ℝ) : ℂ))) ∧
      Tendsto (fun T => cosPairing P D.I D.F ω δ 0 T - cosPairing P D.F D.I ω 0 δ T) atTop
        (𝓝 (∫ t : ℝ, ((Real.cos (ω * t + δ) : ℝ) : ℂ) *
          P.ρ₀ (P.τ t D.I * D.F - D.F * P.τ t D.I))) ∧
      (∫ t : ℝ, ((Real.cos (ω * t + δ) : ℝ) : ℂ) * P.ρ₀ (P.τ t D.I * D.F - D.F * P.τ t D.I)) =
        Complex.I * (ħ : ℂ) *
          ((Complex.exp ((δ : ℂ) * Complex.I) * chiTilde P ħ D.I D.F ω).re : ℂ) := by sorry

end QuantumNoise
