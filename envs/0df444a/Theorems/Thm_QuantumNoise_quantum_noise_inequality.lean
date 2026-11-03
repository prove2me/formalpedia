-- Prove2me | Theorems.Thm_QuantumNoise_quantum_noise_inequality
-- name    : QuantumNoise.quantum_noise_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:50.092912+00:00
-- url     : https://prove2.me/theorems/21e05ef2-9cd3-49fa-9587-7331c84c41f5
-- title:
--   Eqs. (4.11)–(4.12) — the quantum noise inequality
-- statement:
--   Let $(\hat I,\hat F)$ be a detector on a stationary quantum system and $\hbar>0$. For every frequency $\omega$,
--   $$
--   \bar S_{II}[\omega]\bar S_{FF}[\omega]-\big|\bar S_{IF}[\omega]\big|^2\ \ge\ \Big|\frac{\hbar\tilde\chi_{IF}[\omega]}{2}\Big|^2\Big(1+\Delta\Big[\frac{\bar S_{IF}[\omega]}{\hbar\tilde\chi_{IF}[\omega]/2}\Big]\Big),
--   $$
--   where $\tilde\chi_{IF}=\chi_{IF}-\chi_{FI}^\ast$ (4.10) and $\Delta[z]=(|1+z^2|-(1+|z|^2))/2$ (4.12). No equilibrium, gain or symmetry assumption is made: the paper says it "is always valid".
--
--   A detector with gain and without input–output symmetry must therefore have a minimum amount of output and back-action noise, which cannot be perfectly anti-correlated. This constraint is the source of the quantum limits on measurement and amplification in the paper.
--
--   **Formalization Note** When $\tilde\chi_{IF}[\omega]=0$, Lean's $x/0=0$ gives $\Delta[0]=0$ with a zero prefactor, and the statement is the classical inequality (4.9).
--
--   Differences from the source:
--   - encoding: Δ[S̄IF/(ħχ̃IF/2)] at χ̃IF[ω] = 0, where the page's quotient is undefined → Lean's x/0 = 0, so the right side is 0 and the statement is the classical (4.9); reason: the factor |ħχ̃IF/2|² is 0 there, as the page intends; no case is lost
--   - generalization: a detector with Hamiltonian Ĥdet and density matrix ρ̂0, Heisenberg operators Î(t), F̂(t) (p.21) → any unital ∗-algebra over ℂ, any one-parameter group τ of ∗-automorphisms, any τ-invariant state ρ₀ (StationaryDynamics); reason: Heisenberg evolution of a stationary density matrix is such a system; the general form also admits unbounded observables such as the cavity photon number F̂ = n̂ of Sec. III.B
--   - encoding: no regularity stated for the correlators ⟨a(t)b(0)⟩₀ → the correlators ⟨a(t)b⟩₀, a, b ∈ {Î, F̂}, are continuous and integrable on ℝ (fields of Detector); reason: the spectral densities (4.4), (4.7) and gains (4.3), (4.6), (5.49) are Fourier integrals of these correlators and are numbers only when they are integrable; otherwise Lean's integral is 0
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.3, Eqs. (4.11)–(4.12), p.23

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chiTilde
import Definitions.Def_QuantumNoise_Delta

namespace QuantumNoise

/-- **The quantum noise inequality, Eqs. (4.11)–(4.12)** (Clerk et al., arXiv:0810.4729v2, Sec.
IV.A.3, p.23; printed p.23 = PDF p.23): "always valid". For every detector, `ħ > 0` and every
frequency `ω`,
`S̄II[ω] S̄FF[ω] − |S̄IF[ω]|² ≥ |ħ χ̃IF[ω]/2|² (1 + Δ[S̄IF[ω] / (ħ χ̃IF[ω]/2)])`,
with `χ̃IF = χIF − (χFI)*` (4.10) and `Δ[z] = (|1 + z²| − (1 + |z|²))/2` (4.12).

**Formalization Note** No equilibrium, gain or reverse-gain hypothesis. `S̄II`, `S̄FF` are real
(`.re`). When `χ̃IF[ω] = 0`, Lean's `x / 0 = 0` gives `Δ[0] = 0` with a zero prefactor, so the
statement reduces to the classical inequality (4.9), as the page intends. -/
theorem quantum_noise_inequality {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    [StarModule ℂ 𝒜] (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (hħ : 0 < ħ) (ω : ℝ) :
    ‖(ħ : ℂ) * chiTilde P ħ D.I D.F ω / 2‖ ^ 2 *
        (1 + Delta (Sbar P D.I D.F ω / ((ħ : ℂ) * chiTilde P ħ D.I D.F ω / 2))) ≤
      (Sbar P D.I D.I ω).re * (Sbar P D.F D.F ω).re - ‖Sbar P D.I D.F ω‖ ^ 2 := by sorry

end QuantumNoise
