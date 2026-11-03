-- Prove2me | Theorems.Thm_QuantumNoise_addedNoise_ge_optimal_coupling
-- name    : QuantumNoise.addedNoise_ge_optimal_coupling
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:59.883955+00:00
-- url     : https://prove2.me/theorems/fbf7d397-48b7-464f-8ac5-f7f6448a3fa7
-- title:
--   Eq. (5.63) — added noise bound after balancing imprecision and back-action
-- statement:
--   Let $(\hat I,\hat F)$ be a detector, $\hbar>0$, $\omega\in\mathbb R$ with $\chi_{IF}[\omega]\neq0$, a coupling $A\neq0$, $\chi=\chi_{xx}[\omega]\in\mathbb C$ with phase $\varphi=\arg\chi$, and $\sigma=\pm1$. Then
--   $$
--   \bar S_{xx,\rm add}[\omega]\ \ge\ 2|\chi|\left[\sqrt{\frac{\bar S_{II}\bar S_{FF}}{|\chi_{IF}|^2}}+\sigma\,\frac{\operatorname{Re}\big[\chi_{IF}^\ast e^{-i\varphi}\bar S_{IF}\big]}{|\chi_{IF}|^2}\right],
--   $$
--   with $\bar S_{xx,\rm add}$ the added noise (5.61) with cross-term sign $\sigma$ (printed: $\sigma=+1$).
--
--   The bound no longer depends on the coupling $A$; it is reached at the optimal coupling (5.64), which balances measurement imprecision against back-action.
--
--   Differences from the source:
--   - reading: cross term +2Re[χ*IF (χxx)* S̄IF]/|χIF|² of (5.61) → cross term σ·2Re[χ*IF χ* S̄IF]/|χIF|², for both σ = +1 and σ = −1; reason: with χxx of (5.45) and Ĥint = +Ax̂F̂ the cross term of (5.46) has a minus sign, while the printed plus matches the opposite sign convention for χxx used in (5.59); the statement covers both
--   - encoding: S̄xx,add[ω] obtained from the Langevin equations (5.41), (5.44)–(5.46), neglecting non-Gaussian corrections (p.34) → addedNoise is defined as the formula (5.61); reason: the classical-noise derivation is not formalized; the bound is a statement about the expression (5.61)
--   - encoding: divisions by A and by χIF[ω] in (5.61)–(5.66) → hypotheses A ≠ 0 and χIF[ω] ≠ 0; reason: a nondegeneracy condition that only excludes the undefined cases (Lean's x/0 = 0)
--   - generalization: derived in Sec. V.E for a detector with no reverse gain χFI = 0 → no assumption on χFI; reason: the bound follows from (5.61) and X² + Y² ≥ 2|XY| without using χFI; it contains the source's case
--   - generalization: χxx[ω] the damped-oscillator susceptibility (5.45), φ[ω] = arg χxx[ω] → χ an arbitrary complex number, φ = Complex.arg χ; reason: every value of (5.45) is a complex number, so the statement specializes to the oscillator
--   - generalization: a detector with Hamiltonian Ĥdet and density matrix ρ̂0, Heisenberg operators Î(t), F̂(t) (p.21) → any unital ∗-algebra over ℂ, any one-parameter group τ of ∗-automorphisms, any τ-invariant state ρ₀ (StationaryDynamics); reason: Heisenberg evolution of a stationary density matrix is such a system; the general form also admits unbounded observables such as the cavity photon number F̂ = n̂ of Sec. III.B
--   - encoding: no regularity stated for the correlators ⟨a(t)b(0)⟩₀ → the correlators ⟨a(t)b⟩₀, a, b ∈ {Î, F̂}, are continuous and integrable on ℝ (fields of Detector); reason: the spectral densities (4.4), (4.7) and gains (4.3), (4.6), (5.49) are Fourier integrals of these correlators and are numbers only when they are integrable; otherwise Lean's integral is 0
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. V.E.5, Eq. (5.63), p.37

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chi
import Definitions.Def_QuantumNoise_addedNoise

namespace QuantumNoise

/-- **Eq. (5.63)** (Clerk et al., arXiv:0810.4729v2, Sec. V.E.5, p.37; printed p.37 = PDF p.37).
With `φ[ω] = arg χxx[ω]`, the added noise (5.61) satisfies
`S̄xx,add[ω] ≥ 2|χxx[ω]| [√(S̄II S̄FF / |χIF|²) + Re[χIF* e^{−iφ[ω]} S̄IF] / |χIF|²]`.

**Formalization Note** `χ` is an arbitrary complex number standing for `χxx[ω]` and `φ = arg χ`
(`Complex.arg`, with `arg 0 = 0`). The cross term carries the sign `σ = ±1` of `addedNoise`
(printed: `σ = +1`). `A ≠ 0` and `χIF[ω] ≠ 0` exclude Lean's `x / 0 = 0`. -/
theorem addedNoise_ge_optimal_coupling {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    [StarModule ℂ 𝒜] (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (hħ : 0 < ħ)
    (ω : ℝ) (hIF : chi P ħ D.I D.F ω ≠ 0) (A : ℝ) (hA : A ≠ 0) (χ : ℂ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) :
    2 * ‖χ‖ * (Real.sqrt ((Sbar P D.I D.I ω).re * (Sbar P D.F D.F ω).re /
          ‖chi P ħ D.I D.F ω‖ ^ 2) +
        σ * (starRingEnd ℂ (chi P ħ D.I D.F ω) *
          Complex.exp (-((Complex.arg χ : ℂ) * Complex.I)) * Sbar P D.I D.F ω).re /
          ‖chi P ħ D.I D.F ω‖ ^ 2) ≤
      addedNoise P D ħ ω σ A χ := by sorry

end QuantumNoise
