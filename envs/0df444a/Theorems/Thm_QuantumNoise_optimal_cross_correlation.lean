-- Prove2me | Theorems.Thm_QuantumNoise_optimal_cross_correlation
-- name    : QuantumNoise.optimal_cross_correlation
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:24:29.287191+00:00
-- url     : https://prove2.me/theorems/bc9469b8-c0f8-47e5-8b8b-92d8679b474f
-- title:
--   Eqs. (5.67)–(5.68) (corrected: minimizer −σ(ħ/2)cos φ/|sin φ|, not −(ħ/2)cot φ)
-- statement:
--   Let $\hbar>0$, $\sigma=\pm1$ and $\chi=\chi_{xx}[\omega]\in\mathbb C$ with $\operatorname{Im}\chi\neq0$, and let $\varphi=\arg\chi$. For every real $r$ (the value of $\bar S_{IF}/\chi_{IF}$),
--   $$
--   2|\chi|\left[\sqrt{\Big(\frac{\hbar}{2}\Big)^2+r^2}+\sigma\cos\varphi\;r\right]\ \ge\ \hbar\,|\operatorname{Im}\chi| ,
--   $$
--   with equality exactly when
--   $$
--   r=-\sigma\,\frac{\hbar}{2}\,\frac{\cos\varphi}{|\sin\varphi|} .
--   $$
--   So the bound (5.66) is minimized by this cross-correlation, and its minimum is the zero-point noise $\hbar|\operatorname{Im}\chi_{xx}[\omega]|$ (5.68).
--
--   Differences from the source:
--   - correction: the optimal ratio S̄IF[ω]/χIF|optimal = −(ħ/2) cot φ[ω] (5.67) → r = −σ(ħ/2) cos φ/|sin φ|; reason: −(ħ/2)cot φ minimizes √((ħ/2)² + r²) + r cos φ only when sin φ > 0; example σ = 1, φ = −π/4, ħ = 2: the bracket is 0.707 at the true minimizer r = −1 and 2.12 at the printed r = +1
--   - reading: "we can minimize the expression over its value" (the right side of (5.66) as a function of the real ratio S̄IF/χIF), with minimum value (5.68) → the function r ↦ 2|χ|(√((ħ/2)² + r²) + σ r cos φ) on ℝ, its lower bound ħ|Im χ| and the equality case; reason: the page minimizes the bound (5.66) over the value of the ratio; this is that minimization
--   - reading: cross term +2Re[χ*IF (χxx)* S̄IF]/|χIF|² of (5.61) → cross term σ·2Re[χ*IF χ* S̄IF]/|χIF|², for both σ = +1 and σ = −1; reason: with χxx of (5.45) and Ĥint = +Ax̂F̂ the cross term of (5.46) has a minus sign, while the printed plus matches the opposite sign convention for χxx used in (5.59); the statement covers both
--   - encoding: minimum = ħ|Im χxx[ω]| = lim_{T→0} S̄xx,eq[ω, T] (5.68) → minimum ħ|Im χ|; S̄xx,eq (5.59) is not defined; reason: (5.68) itself identifies the limit with ħ|Im χxx|
--   - generalization: χxx[ω] the damped-oscillator susceptibility (5.45), φ[ω] = arg χxx[ω] → χ an arbitrary complex number, φ = Complex.arg χ; reason: every value of (5.45) is a complex number, so the statement specializes to the oscillator
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. V.E.5, Eqs. (5.67)–(5.68), p.38

import Mathlib

namespace QuantumNoise

/-- **Eqs. (5.67)–(5.68)**, corrected sign (Clerk et al., arXiv:0810.4729v2, Sec. V.E.5, p.38;
printed p.38 = PDF p.38). Minimizing the bound (5.66) over the real value `r = S̄IF/χIF`: for
`ħ > 0`, `χ = χxx[ω]` with `Im χ ≠ 0`, `φ = arg χ` and `σ = ±1`,
`2|χ| [√((ħ/2)² + r²) + σ r cos φ] ≥ ħ |Im χ|` for every real `r`, with equality exactly at
`r = −σ (ħ/2) cos φ / |sin φ|`.

**Formalization Note** The page prints the minimizer as `−(ħ/2) cot φ[ω]`, which is correct only
for `sin φ > 0`; the minimizer for every `φ` with `sin φ ≠ 0` and both cross-term signs is
`−σ (ħ/2) cos φ / |sin φ|` (correction). `Im χ ≠ 0` is `sin φ ≠ 0`. The minimum value
`ħ |Im χxx[ω]|` is (5.68). -/
theorem optimal_cross_correlation (ħ : ℝ) (hħ : 0 < ħ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (χ : ℂ)
    (hχ : χ.im ≠ 0) :
    (∀ r : ℝ, ħ * |χ.im| ≤
        2 * ‖χ‖ * (Real.sqrt ((ħ / 2) ^ 2 + r ^ 2) + σ * Real.cos (Complex.arg χ) * r)) ∧
      ∀ r : ℝ, 2 * ‖χ‖ * (Real.sqrt ((ħ / 2) ^ 2 + r ^ 2) + σ * Real.cos (Complex.arg χ) * r) =
          ħ * |χ.im| ↔
        r = -σ * (ħ / 2) * Real.cos (Complex.arg χ) / |Real.sin (Complex.arg χ)| := by sorry

end QuantumNoise
