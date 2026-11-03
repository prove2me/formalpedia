-- Prove2me | Theorems.Thm_QuantumNoise_addedNoise_ge_real_ratio
-- name    : QuantumNoise.addedNoise_ge_real_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:54.907869+00:00
-- url     : https://prove2.me/theorems/7307be07-0cf5-4765-9da1-d3f5330be6d4
-- title:
--   Eq. (5.66) (corrected: exact hypothesis Im(S̄IF/χIF) = 0 in place of large power gain)
-- statement:
--   Let $(\hat I,\hat F)$ be a detector, $\hbar>0$, and $\omega$ a frequency with $\chi_{FI}[\omega]=0$ and $\chi_{IF}[\omega]\neq0$, such that the ratio $r=\bar S_{IF}[\omega]/\chi_{IF}[\omega]$ is real. Let $A\neq0$, $\chi=\chi_{xx}[\omega]\in\mathbb C$, $\varphi=\arg\chi$ and $\sigma=\pm1$. Then
--   $$
--   \bar S_{xx,\rm add}[\omega]\ \ge\ 2|\chi|\left[\sqrt{\Big(\frac{\hbar}{2}\Big)^2+r^2}+\sigma\cos\varphi\;r\right].
--   $$
--   The page states this for a detector with large power gain, arguing that large gain makes $\bar S_{IF}/\chi_{IF}$ real; the exact hypothesis is that the ratio is real.
--
--   Differences from the source:
--   - correction: large power gain GP[ω] ≫ 1, "this implies that the ratio S̄IF/χIF is purely real, up to small ħω/(kBTeff) corrections" (pp.37–38) → the hypothesis Im(S̄IF[ω]/χIF[ω]) = 0; reason: the inference holds only for detectors with ideal noise (4.17) (Appendix I.3 assumes it); counterexample with every assumption of the page: ħ = 1, ω > 0, χFI = 0, χIF[ω] = 1, χ = i, S̄IF = iv with v > 0, passive spectra SII[±ω] = S̄II(1 ± E), SFF[±ω] = S̄FF(1 ± ε), S̄IIS̄FF ≈ v² + 1/4, ε → 0⁺: GP → ∞ while the added noise at the optimal A is (√(1 + 4v²) − 2v)ħ|Im χ| (0.41, 0.16, 0.05 of the bound at v = 0.5, 1.5, 5; planning_numerics/c1_counterexample.py)
--   - reading: cross term +2Re[χ*IF (χxx)* S̄IF]/|χIF|² of (5.61) → cross term σ·2Re[χ*IF χ* S̄IF]/|χIF|², for both σ = +1 and σ = −1; reason: with χxx of (5.45) and Ĥint = +Ax̂F̂ the cross term of (5.46) has a minus sign, while the printed plus matches the opposite sign convention for χxx used in (5.59); the statement covers both
--   - encoding: S̄xx,add[ω] obtained from the Langevin equations (5.41), (5.44)–(5.46), neglecting non-Gaussian corrections (p.34) → addedNoise is defined as the formula (5.61); reason: the classical-noise derivation is not formalized; the bound is a statement about the expression (5.61)
--   - encoding: divisions by A and by χIF[ω] in (5.61)–(5.66) → hypotheses A ≠ 0 and χIF[ω] ≠ 0; reason: a nondegeneracy condition that only excludes the undefined cases (Lean's x/0 = 0)
--   - generalization: no reverse gain χFI = 0 (Sec. V.E.3, "the idea case of no reverse gain") → χFI[ω] = 0 at the frequency ω only; reason: χFI = 0 at all frequencies implies it at ω; the proof uses only the value at ω
--   - generalization: χxx[ω] the damped-oscillator susceptibility (5.45), φ[ω] = arg χxx[ω] → χ an arbitrary complex number, φ = Complex.arg χ; reason: every value of (5.45) is a complex number, so the statement specializes to the oscillator
--   - generalization: a detector with Hamiltonian Ĥdet and density matrix ρ̂0, Heisenberg operators Î(t), F̂(t) (p.21) → any unital ∗-algebra over ℂ, any one-parameter group τ of ∗-automorphisms, any τ-invariant state ρ₀ (StationaryDynamics); reason: Heisenberg evolution of a stationary density matrix is such a system; the general form also admits unbounded observables such as the cavity photon number F̂ = n̂ of Sec. III.B
--   - encoding: no regularity stated for the correlators ⟨a(t)b(0)⟩₀ → the correlators ⟨a(t)b⟩₀, a, b ∈ {Î, F̂}, are continuous and integrable on ℝ (fields of Detector); reason: the spectral densities (4.4), (4.7) and gains (4.3), (4.6), (5.49) are Fourier integrals of these correlators and are numbers only when they are integrable; otherwise Lean's integral is 0
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. V.E.5, Eq. (5.66), pp.37–38

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chi
import Definitions.Def_QuantumNoise_addedNoise

namespace QuantumNoise

/-- **Eq. (5.66)**, corrected hypothesis (Clerk et al., arXiv:0810.4729v2, Sec. V.E.5, pp.37–38;
printed = PDF pages). For a detector with no reverse gain at `ω` whose ratio `S̄IF[ω]/χIF[ω]` is
real,
`S̄xx,add[ω] ≥ 2|χxx[ω]| [√((ħ/2)² + (S̄IF/χIF)²) + cos[φ[ω]] S̄IF/χIF]`.

**Formalization Note** The page assumes a large power gain `GP[ω] ≫ 1` and infers that
`S̄IF/χIF` is real "up to small corrections"; that inference holds only for detectors with ideal
noise (4.17), so the exact hypothesis `Im(S̄IF[ω]/χIF[ω]) = 0` is assumed instead (correction).
`χ` stands for `χxx[ω]`, `φ = arg χ`; the cross term carries the sign `σ = ±1` (printed
`σ = +1`). `S̄IF/χIF` enters through its real part. -/
theorem addedNoise_ge_real_ratio {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    [StarModule ℂ 𝒜] (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (hħ : 0 < ħ)
    (ω : ℝ) (hFI : chi P ħ D.F D.I ω = 0) (hIF : chi P ħ D.I D.F ω ≠ 0) (A : ℝ) (hA : A ≠ 0)
    (χ : ℂ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hreal : (Sbar P D.I D.F ω / chi P ħ D.I D.F ω).im = 0) :
    2 * ‖χ‖ * (Real.sqrt ((ħ / 2) ^ 2 + (Sbar P D.I D.F ω / chi P ħ D.I D.F ω).re ^ 2) +
        σ * Real.cos (Complex.arg χ) * (Sbar P D.I D.F ω / chi P ħ D.I D.F ω).re) ≤
      addedNoise P D ħ ω σ A χ := by sorry

end QuantumNoise
