-- Prove2me | Theorems.Thm_QuantumNoise_addedNoise_ge_quantum_constraint
-- name    : QuantumNoise.addedNoise_ge_quantum_constraint
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:13.288784+00:00
-- url     : https://prove2.me/theorems/128b3867-b092-4238-ab8f-169e223f04e6
-- title:
--   Eq. (5.65) — added noise bound from the quantum noise constraint
-- statement:
--   Let $(\hat I,\hat F)$ be a detector, $\hbar>0$, and $\omega$ a frequency with no reverse gain, $\chi_{FI}[\omega]=0$, and $\chi_{IF}[\omega]\neq0$. Let $A\neq0$, $\chi=\chi_{xx}[\omega]\in\mathbb C$, $\varphi=\arg\chi$ and $\sigma=\pm1$. Then
--   $$
--   \bar S_{xx,\rm add}[\omega]\ \ge\ 2\left|\frac{\chi}{\chi_{IF}}\right|\left[\sqrt{\Big(\frac{\hbar|\chi_{IF}|}{2}\Big)^2\Big(1+\Delta\Big[\frac{2\bar S_{IF}}{\hbar\chi_{IF}}\Big]\Big)+|\bar S_{IF}|^2}+\sigma\,\frac{\operatorname{Re}\big[\chi_{IF}^\ast e^{-i\varphi}\bar S_{IF}\big]}{|\chi_{IF}|}\right].
--   $$
--   It combines (5.63) with the quantum noise inequality (4.11); the minimum of $\bar S_{xx,\rm add}$ needs both the optimal coupling (5.64) and a detector satisfying (4.11) with equality.
--
--   Differences from the source:
--   - reading: cross term +2Re[χ*IF (χxx)* S̄IF]/|χIF|² of (5.61) → cross term σ·2Re[χ*IF χ* S̄IF]/|χIF|², for both σ = +1 and σ = −1; reason: with χxx of (5.45) and Ĥint = +Ax̂F̂ the cross term of (5.46) has a minus sign, while the printed plus matches the opposite sign convention for χxx used in (5.59); the statement covers both
--   - encoding: S̄xx,add[ω] obtained from the Langevin equations (5.41), (5.44)–(5.46), neglecting non-Gaussian corrections (p.34) → addedNoise is defined as the formula (5.61); reason: the classical-noise derivation is not formalized; the bound is a statement about the expression (5.61)
--   - encoding: divisions by A and by χIF[ω] in (5.61)–(5.66) → hypotheses A ≠ 0 and χIF[ω] ≠ 0; reason: a nondegeneracy condition that only excludes the undefined cases (Lean's x/0 = 0)
--   - generalization: no reverse gain χFI = 0 (Sec. V.E.3, "the idea case of no reverse gain") → χFI[ω] = 0 at the frequency ω only; reason: χFI = 0 at all frequencies implies it at ω; the proof uses only the value at ω
--   - generalization: χxx[ω] the damped-oscillator susceptibility (5.45), φ[ω] = arg χxx[ω] → χ an arbitrary complex number, φ = Complex.arg χ; reason: every value of (5.45) is a complex number, so the statement specializes to the oscillator
--   - generalization: a detector with Hamiltonian Ĥdet and density matrix ρ̂0, Heisenberg operators Î(t), F̂(t) (p.21) → any unital ∗-algebra over ℂ, any one-parameter group τ of ∗-automorphisms, any τ-invariant state ρ₀ (StationaryDynamics); reason: Heisenberg evolution of a stationary density matrix is such a system; the general form also admits unbounded observables such as the cavity photon number F̂ = n̂ of Sec. III.B
--   - encoding: no regularity stated for the correlators ⟨a(t)b(0)⟩₀ → the correlators ⟨a(t)b⟩₀, a, b ∈ {Î, F̂}, are continuous and integrable on ℝ (fields of Detector); reason: the spectral densities (4.4), (4.7) and gains (4.3), (4.6), (5.49) are Fourier integrals of these correlators and are numbers only when they are integrable; otherwise Lean's integral is 0
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. V.E.5, Eq. (5.65), p.37

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chi
import Definitions.Def_QuantumNoise_Delta
import Definitions.Def_QuantumNoise_addedNoise

namespace QuantumNoise

/-- **Eq. (5.65)** (Clerk et al., arXiv:0810.4729v2, Sec. V.E.5, p.37; printed p.37 = PDF p.37).
For a detector with no reverse gain at `ω` (`χFI[ω] = 0`), using the quantum noise constraint
(4.11) to bound (5.63):
`S̄xx,add[ω] ≥ 2|χxx[ω]/χIF| × [√((ħ|χIF|/2)² (1 + Δ[2S̄IF/(ħχIF)]) + |S̄IF|²)
  + Re[χIF* e^{−iφ[ω]} S̄IF] / |χIF|]`.

**Formalization Note** `χ` is an arbitrary complex number standing for `χxx[ω]`, `φ = arg χ`;
the cross term carries the sign `σ = ±1` (printed `σ = +1`). No reverse gain is assumed only at
the frequency `ω`. `A ≠ 0`, `χIF[ω] ≠ 0` exclude Lean's `x / 0 = 0`. -/
theorem addedNoise_ge_quantum_constraint {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    [StarModule ℂ 𝒜] (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (hħ : 0 < ħ)
    (ω : ℝ) (hFI : chi P ħ D.F D.I ω = 0) (hIF : chi P ħ D.I D.F ω ≠ 0) (A : ℝ) (hA : A ≠ 0)
    (χ : ℂ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    2 * ‖χ / chi P ħ D.I D.F ω‖ *
        (Real.sqrt ((ħ * ‖chi P ħ D.I D.F ω‖ / 2) ^ 2 *
            (1 + Delta (2 * Sbar P D.I D.F ω / ((ħ : ℂ) * chi P ħ D.I D.F ω))) +
            ‖Sbar P D.I D.F ω‖ ^ 2) +
          σ * (starRingEnd ℂ (chi P ħ D.I D.F ω) *
            Complex.exp (-((Complex.arg χ : ℂ) * Complex.I)) * Sbar P D.I D.F ω).re /
            ‖chi P ħ D.I D.F ω‖) ≤
      addedNoise P D ħ ω σ A χ := by sorry

end QuantumNoise
