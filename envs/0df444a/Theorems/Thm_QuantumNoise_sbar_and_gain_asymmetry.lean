-- Prove2me | Theorems.Thm_QuantumNoise_sbar_and_gain_asymmetry
-- name    : QuantumNoise.sbar_and_gain_asymmetry
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:24.946591+00:00
-- url     : https://prove2.me/theorems/d62248e9-9a3b-4269-8279-f1731b443f97
-- title:
--   Eqs. (4.8a)–(4.8b) — $\bar S_{IF}$ and the gain asymmetry from $S_{IF}[\pm\omega]$
-- statement:
--   Let $(\hat I,\hat F)$ be a detector on a stationary quantum system and $\hbar>0$. For every frequency $\omega\in\mathbb R$,
--   $$
--   \bar S_{IF}[\omega]=\frac12\big[S_{IF}[\omega]+S_{IF}[-\omega]^\ast\big],\qquad
--   \chi_{IF}[\omega]-\chi_{FI}[\omega]^\ast=-\frac{i}{\hbar}\big[S_{IF}[\omega]-S_{IF}[-\omega]^\ast\big].
--   $$
--   Here $\bar S_{IF}$ is the symmetrized cross spectrum (4.4c), $S_{IF}$ the unsymmetrized one (4.7), and $\chi_{IF}$, $\chi_{FI}$ the gain and reverse gain (4.3), (4.6).
--
--   So the symmetrized cross spectrum is the classical part of $S_{IF}$, and the gains are fixed by its quantum (frequency-asymmetric) part; this is what makes the gains enter the quantum noise constraint.
--
--   Differences from the source:
--   - generalization: a detector with Hamiltonian Ĥdet and density matrix ρ̂0, Heisenberg operators Î(t), F̂(t) (p.21) → any unital ∗-algebra over ℂ, any one-parameter group τ of ∗-automorphisms, any τ-invariant state ρ₀ (StationaryDynamics); reason: Heisenberg evolution of a stationary density matrix is such a system; the general form also admits unbounded observables such as the cavity photon number F̂ = n̂ of Sec. III.B
--   - encoding: no regularity stated for the correlators ⟨a(t)b(0)⟩₀ → the correlators ⟨a(t)b⟩₀, a, b ∈ {Î, F̂}, are continuous and integrable on ℝ (fields of Detector); reason: the spectral densities (4.4), (4.7) and gains (4.3), (4.6), (5.49) are Fourier integrals of these correlators and are numbers only when they are integrable; otherwise Lean's integral is 0
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.2, Eqs. (4.8a)–(4.8b), p.22

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_S
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chi

namespace QuantumNoise

/-- **Eqs. (4.8a)–(4.8b)** (Clerk et al., arXiv:0810.4729v2, Sec. IV.A.2, p.22; printed p.22 = PDF
p.22). For a detector, `ħ > 0` and every frequency `ω`,
`S̄IF[ω] = ½ [SIF[ω] + SIF[−ω]*]` and `χIF[ω] − χFI[ω]* = −(i/ħ) [SIF[ω] − SIF[−ω]*]`.

**Formalization Note** `S̄IF` is the anticommutator transform (4.4c), `SIF` the unsymmetrized
spectrum (4.7), `χIF`, `χFI` the Kubo gains (4.3), (4.6); Fourier sign `e^{+iωt}` (Table I).
Correlators are integrable (`Detector`). -/
theorem sbar_and_gain_asymmetry {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    [StarModule ℂ 𝒜] (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (hħ : 0 < ħ) (ω : ℝ) :
    Sbar P D.I D.F ω = (1 / 2 : ℂ) * (S P D.I D.F ω + starRingEnd ℂ (S P D.I D.F (-ω))) ∧
      chi P ħ D.I D.F ω - starRingEnd ℂ (chi P ħ D.F D.I ω) =
        -(Complex.I / (ħ : ℂ)) * (S P D.I D.F ω - starRingEnd ℂ (S P D.I D.F (-ω))) := by sorry

end QuantumNoise
