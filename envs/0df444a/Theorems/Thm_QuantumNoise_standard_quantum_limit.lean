-- Prove2me | Theorems.Thm_QuantumNoise_standard_quantum_limit
-- name    : QuantumNoise.standard_quantum_limit
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:05.051493+00:00
-- url     : https://prove2.me/theorems/f22a4746-1124-412d-a0ba-8073fe67d5fd
-- title:
--   Standard quantum limit on the added noise, Eq. (5.62) (corrected: exact phase hypothesis; finite-gain bound for ideal detectors; |sin φ| in (5.67))
-- statement:
--   Let $(\hat I,\hat F)$ be a detector on a stationary quantum system, $\hbar>0$, and $\omega$ a frequency with no reverse gain, $\chi_{FI}[\omega]=0$, and $\chi_{IF}[\omega]\neq0$. Let $A\neq0$ be the coupling, $\chi=\chi_{xx}[\omega]\in\mathbb C$ the oscillator susceptibility with phase $\varphi=\arg\chi$, $\sigma=\pm1$ the sign of the cross term, and $\bar S_{xx,\rm add}[\omega]$ the added noise (5.61). Then:
--
--   1. **(exact limit)** if $\bar S_{IF}[\omega]/\chi_{IF}[\omega]$ is real, then
--   $$
--   \bar S_{xx,\rm add}[\omega]\ \ge\ \hbar\,|\operatorname{Im}\chi| ;
--   $$
--   2. **(attainment)** if moreover $\operatorname{Im}\chi\neq0$, the detector has ideal noise (4.17) at $\omega$, the coupling satisfies $A^4|\chi_{IF}\chi|^2\bar S_{FF}=\bar S_{II}$ (5.64), and $\bar S_{IF}/\chi_{IF}=-\sigma\frac{\hbar}{2}\frac{\cos\varphi}{|\sin\varphi|}$ (5.67), then $\bar S_{xx,\rm add}[\omega]=\hbar|\operatorname{Im}\chi|$;
--   3. **(ideal detectors at finite gain)** if the detector has ideal noise (4.17) at $\omega$, $\operatorname{Im}\chi_{FF}[\omega]\cdot\operatorname{Im}\chi_{II}[\omega]>0$, $G=G_P[\omega]$ is the power gain (5.52), $s=|\sin\varphi|$, $c=|\cos\varphi|$, and $1-s/\sqrt G>c$, then
--   $$
--   \bar S_{xx,\rm add}[\omega]\ \ge\ \hbar\,|\chi|\sqrt{s^2\Big(1+\frac1G\Big)-\frac{2s}{\sqrt G}} ,
--   $$
--   whose right side tends to $\hbar|\operatorname{Im}\chi|$ as $G\to\infty$.
--
--   The page states: "if our detector has a large power gain, the spectral density of the noise added by the detector (i.e. $\bar S_{xx,\rm add}[\omega]$) must be at least as big as the zero point noise of our damped oscillator: $\bar S_{xx,\rm add}[\omega]\ge\lim_{T\to0}\bar S_{xx,\rm eq}[\omega,T]=|\hbar\operatorname{Im}\chi_{xx}[\omega]|$ (5.62)", and that this bound "is rigorously correct at each frequency $\omega$". This is the linear-response form of the amplifier quantum limit: a position detector with large power gain adds at least the zero-point noise of the oscillator it measures.
--
--   **Formalization Note** In clause 3 the hypothesis $1-s/\sqrt G>c$ makes the radicand positive, so the square root is never evaluated at a negative number.
--
--   Differences from the source:
--   - correction: large power gain GP[ω] ≫ 1, "this implies that the ratio S̄IF/χIF is purely real, up to small ħω/(kBTeff) corrections" (pp.37–38); (5.62) for every detector with large power gain → clause (a) with the exact hypothesis Im(S̄IF[ω]/χIF[ω]) = 0, and clause (c), the large-gain bound for detectors with ideal noise (4.17), with the explicit finite-gain right side ħ|χ|√(s²(1 + 1/G) − 2s/√G); reason: the inference holds only for detectors with ideal noise (4.17) (Appendix I.3 assumes it); counterexample with every assumption of the page: ħ = 1, ω > 0, χFI = 0, χIF[ω] = 1, χ = i, S̄IF = iv with v > 0, passive spectra SII[±ω] = S̄II(1 ± E), SFF[±ω] = S̄FF(1 ± ε), S̄IIS̄FF ≈ v² + 1/4, ε → 0⁺: GP → ∞ while the added noise at the optimal A is (√(1 + 4v²) − 2v)ħ|Im χ| (0.41, 0.16, 0.05 of the bound at v = 0.5, 1.5, 5; planning_numerics/c1_counterexample.py); for an ideal detector with no reverse gain the page's claim holds, in the exact form of clause (c), which tends to ħ|Im χ| as G → ∞
--   - correction: the optimal ratio S̄IF/χIF|optimal = −(ħ/2) cot φ[ω] (5.67) in the attainment conditions → S̄IF/χIF = −σ(ħ/2) cos φ/|sin φ| in clause (b); reason: −(ħ/2)cot φ is the minimizer only for sin φ > 0; example σ = 1, φ = −π/4, ħ = 2: the bracket of (5.66) is 0.707 at r = −1 and 2.12 at the printed r = +1
--   - reading: cross term +2Re[χ*IF (χxx)* S̄IF]/|χIF|² of (5.61) → cross term σ·2Re[χ*IF χ* S̄IF]/|χIF|², for both σ = +1 and σ = −1; reason: with χxx of (5.45) and Ĥint = +Ax̂F̂ the cross term of (5.46) has a minus sign, while the printed plus matches the opposite sign convention for χxx used in (5.59); the statement covers both
--   - reading: the power gain GP[ω] (5.52) in "a large power gain" → clause (c) assumes Im χFF[ω]·Im χII[ω] > 0 and uses G = |χIF|²/(4 Im χFF Im χII); reason: (5.52) is a ratio of absorbed powers (5.47)–(5.51), a gain only when both dampings are positive
--   - encoding: S̄xx,add[ω] obtained from the Langevin equations (5.41), (5.44)–(5.46), neglecting non-Gaussian corrections (p.34) → addedNoise is defined as the formula (5.61); reason: the classical-noise derivation is not formalized; the bound is a statement about the expression (5.61)
--   - encoding: no regularity stated for the correlators ⟨a(t)b(0)⟩₀ → the correlators ⟨a(t)b⟩₀, a, b ∈ {Î, F̂}, are continuous and integrable on ℝ (fields of Detector); reason: the spectral densities (4.4), (4.7) and gains (4.3), (4.6), (5.49) are Fourier integrals of these correlators and are numbers only when they are integrable; otherwise Lean's integral is 0
--   - encoding: divisions by A and by χIF[ω] in (5.61)–(5.66) → hypotheses A ≠ 0 and χIF[ω] ≠ 0; reason: a nondegeneracy condition that only excludes the undefined cases (Lean's x/0 = 0)
--   - encoding: right side lim_{T→0} S̄xx,eq[ω, T] = |ħ Im χxx[ω]| with S̄xx,eq from (5.59) → right side ħ|Im χ|; S̄xx,eq is not defined; reason: (5.62) itself identifies the limit with |ħ Im χxx|, so the inequality is the same
--   - generalization: χxx[ω] the damped-oscillator susceptibility (5.45), φ[ω] = arg χxx[ω] → χ an arbitrary complex number, φ = Complex.arg χ; reason: every value of (5.45) is a complex number, so the statement specializes to the oscillator
--   - generalization: no reverse gain χFI = 0 (Sec. V.E.3, "the idea case of no reverse gain") → χFI[ω] = 0 at the frequency ω only; reason: χFI = 0 at all frequencies implies it at ω; the proof uses only the value at ω
--   - generalization: a detector with Hamiltonian Ĥdet and density matrix ρ̂0, Heisenberg operators Î(t), F̂(t) (p.21) → any unital ∗-algebra over ℂ, any one-parameter group τ of ∗-automorphisms, any τ-invariant state ρ₀ (StationaryDynamics); reason: Heisenberg evolution of a stationary density matrix is such a system; the general form also admits unbounded observables such as the cavity photon number F̂ = n̂ of Sec. III.B
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. V.E.5, Eq. (5.62), p.37, with Eqs. (5.64), (5.66)–(5.68) and conditions 1–3, p.38

import Mathlib
import Definitions.Def_QuantumNoise_Detector
import Definitions.Def_QuantumNoise_Sbar
import Definitions.Def_QuantumNoise_chi
import Definitions.Def_QuantumNoise_IdealNoise
import Definitions.Def_QuantumNoise_powerGain
import Definitions.Def_QuantumNoise_addedNoise

namespace QuantumNoise

/-- **The standard quantum limit on the added noise of a linear position detector, Eq. (5.62)
with (5.66)–(5.68)**, corrected (Clerk et al., arXiv:0810.4729v2, Sec. V.E.5, p.37 and p.38;
printed = PDF pages). Printed: "if our detector has a large power gain, the spectral density of
the noise added by the detector (i.e. S̄xx,add[ω]) must be at least as big as the zero point
noise of our damped oscillator: S̄xx,add[ω] ≥ lim_{T→0} S̄xx,eq[w, T] = |ħ Im χxx[ω]| (5.62). We
will now show that the bound above is rigorously correct at each frequency ω."

Let a detector have no reverse gain at `ω` (`χFI[ω] = 0`) and `χIF[ω] ≠ 0`; let `A ≠ 0`,
`χ = χxx[ω] ∈ ℂ`, `φ = arg χ`, `σ = ±1`, and `S̄add = addedNoise` (5.61). Then:
(a) if `S̄IF[ω]/χIF[ω]` is real, `S̄add ≥ ħ |Im χ|`;
(b) if moreover `Im χ ≠ 0`, the detector has ideal noise (4.17) at `ω`, the coupling satisfies
`A⁴ |χIF χ|² S̄FF = S̄II` (5.64), and `S̄IF/χIF = −σ (ħ/2) cos φ / |sin φ|` ((5.67), corrected),
then `S̄add = ħ |Im χ|`;
(c) if the detector has ideal noise (4.17) at `ω`, `Im χFF[ω] · Im χII[ω] > 0`, `G = GP[ω]`
(5.52), `s = |sin φ|`, `c = |cos φ|` and `1 − s/√G > c`, then
`S̄add ≥ ħ |χ| √(s² (1 + 1/G) − 2 s/√G)` (which tends to `ħ |Im χ|` as `G → ∞`).

**Formalization Note** Corrections. The page's step "large power gain implies `S̄IF/χIF` real" holds
only for detectors with ideal noise; for a non-ideal detector with no reverse gain the added noise
can stay far below `ħ|Im χxx|` at arbitrarily large power gain. Clause (a) is the bound with the
exact phase hypothesis, clause (c) the large-gain statement for ideal detectors with an explicit
finite-gain bound, clause (b) attainment (conditions 1–3 of p.38). The minimizer `−(ħ/2) cot φ` of
(5.67) is corrected to `−σ(ħ/2) cos φ/|sin φ|`. Conventions: (5.61) is the definition of the added
noise and `χ` is an arbitrary complex number; `σ` is the sign of the cross term (the printed
formula is `σ = +1`); the right side of (5.62) is written `ħ|Im χ|` (`lim_{T→0}` of (5.59) is not
formalized). In (c), the hypothesis `1 − s/√G > c` makes the radicand positive, so
`Real.sqrt` is not evaluated on a negative number. `A ≠ 0` and `χIF ≠ 0` exclude `x / 0 = 0`. -/
theorem standard_quantum_limit {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    [StarModule ℂ 𝒜] (P : StationaryDynamics 𝒜) (D : Detector P) (ħ : ℝ) (hħ : 0 < ħ)
    (ω : ℝ) (hFI : chi P ħ D.F D.I ω = 0) (hIF : chi P ħ D.I D.F ω ≠ 0) (A : ℝ) (hA : A ≠ 0)
    (χ : ℂ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ((Sbar P D.I D.F ω / chi P ħ D.I D.F ω).im = 0 →
        ħ * |χ.im| ≤ addedNoise P D ħ ω σ A χ) ∧
      (χ.im ≠ 0 → IdealNoise P D ħ ω →
        A ^ 4 * ‖chi P ħ D.I D.F ω * χ‖ ^ 2 * (Sbar P D.F D.F ω).re = (Sbar P D.I D.I ω).re →
        Sbar P D.I D.F ω / chi P ħ D.I D.F ω =
          ((-σ * (ħ / 2) * Real.cos (Complex.arg χ) / |Real.sin (Complex.arg χ)| : ℝ) : ℂ) →
        addedNoise P D ħ ω σ A χ = ħ * |χ.im|) ∧
      (IdealNoise P D ħ ω →
        0 < (chi P ħ D.F D.F ω).im * (chi P ħ D.I D.I ω).im →
        |Real.cos (Complex.arg χ)| <
          1 - |Real.sin (Complex.arg χ)| / Real.sqrt (powerGain P D ħ ω) →
        ħ * ‖χ‖ * Real.sqrt (|Real.sin (Complex.arg χ)| ^ 2 * (1 + 1 / powerGain P D ħ ω) -
            2 * |Real.sin (Complex.arg χ)| / Real.sqrt (powerGain P D ħ ω)) ≤
          addedNoise P D ħ ω σ A χ) := by sorry

end QuantumNoise
