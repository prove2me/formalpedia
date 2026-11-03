-- Prove2me | Theorems.Thm_QuantumNoise_noise_bound_phase
-- name    : QuantumNoise.noise_bound_phase
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:38.264753+00:00
-- url     : https://prove2.me/theorems/bfb60d95-4c82-40ab-b939-17ad33ed7774
-- title:
--   Eq. (4.16) — the phase-resolved quantum noise bound
-- statement:
--   Let $(\hat I,\hat F)$ be a detector and $\hbar>0$. For every frequency $\omega$ and every real phase $\delta$,
--   $$
--   \bar S_{II}[\omega]\bar S_{FF}[\omega]\ \ge\ \Big[\operatorname{Re}\big(e^{i\delta}\bar S_{IF}[\omega]\big)\Big]^2+\frac{\hbar^2}{4}\Big[\operatorname{Re}\,e^{i\delta}\big(\chi_{IF}[\omega]-(\chi_{FI}[\omega])^\ast\big)\Big]^2 .
--   $$
--   Maximizing the right side over $\delta$ gives the quantum noise inequality (4.11).
--
--   Differences from the source:
--   - generalization: (4.16) derived from (4.15), stated there for ω ≠ 0 → every ω ∈ ℝ, including ω = 0; reason: contains the source's case ω ≠ 0
--   - generalization: a detector with Hamiltonian Ĥdet and density matrix ρ̂0, Heisenberg operators Î(t), F̂(t) (p.21) → any unital ∗-algebra over ℂ, any one-parameter group τ of ∗-automorphisms, any τ-invariant state ρ₀ (StationaryDynamics); reason: Heisenberg evolution of a stationary density matrix is such a system; the general form also admits unbounded observables such as the cavity photon number F̂ = n̂ of Sec. III.B
--   - encoding: no regularity stated for the correlators ⟨a(t)b(0)⟩₀ → the correlators ⟨a(t)b⟩₀, a, b ∈ {Î, F̂}, are continuous and integrable on ℝ (fields of Detector); reason: the spectral densities (4.4), (4.7) and gains (4.3), (4.6), (5.49) are Fourier integrals of these correlators and are numbers only when they are integrable; otherwise Lean's integral is 0
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.3, Eq. (4.16), p.23

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chiTilde

namespace QuantumNoise

/-- **Eq. (4.16)** (Clerk et al., arXiv:0810.4729v2, Sec. IV.A.3, p.23; printed p.23 = PDF p.23).
For a detector, `ħ > 0`, every frequency `ω` and every real phase `δ`,
`S̄II[ω] S̄FF[ω] ≥ [Re(e^{iδ} S̄IF[ω])]² + (ħ²/4) [Re e^{iδ}(χIF[ω] − (χFI[ω])*)]²`.

**Formalization Note** `S̄II`, `S̄FF` are real (`.re`); `χIF − (χFI)*` is `chiTilde`. The page
derives (4.16) from (4.15), stated for `ω ≠ 0`; the inequality is stated here for every `ω`. -/
theorem noise_bound_phase {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (hħ : 0 < ħ) (ω δ : ℝ) :
    ((Complex.exp ((δ : ℂ) * Complex.I) * Sbar P D.I D.F ω).re) ^ 2 +
        ħ ^ 2 / 4 * ((Complex.exp ((δ : ℂ) * Complex.I) * chiTilde P ħ D.I D.F ω).re) ^ 2 ≤
      (Sbar P D.I D.I ω).re * (Sbar P D.F D.F ω).re := by sorry

end QuantumNoise
