-- Prove2me | Theorems.Thm_SobolevL2_sobolevNorm_schwartz_eq_lintegral_fourier
-- name    : SobolevL2.sobolevNorm_schwartz_eq_lintegral_fourier
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:42.215347+00:00
-- url     : https://prove2.me/theorems/8e168e53-d3e9-44be-afc7-00f81fe29d2a
-- title:
--   Sobolev norm of a Schwartz function: $\|\varphi\|_{H^s}^2=\int(1+|\xi|^2)^s|\widehat\varphi(\xi)|^2\,d\xi$
-- statement:
--   **The $H^s$ norm of a Schwartz function.** Let $E$ be a finite-dimensional real inner product space (a copy of $\mathbb R^n$, $n=\dim E$) with its Lebesgue measure, let $F$ be a complex Hilbert space (the classical case is $F=\mathbb C$), and let $\mathcal S(E,F)$, $\mathcal S'(E,F)$ be the Schwartz functions and the tempered distributions. The Fourier transform is $\widehat f(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$, extended to $\mathcal S'$ by duality. For $s\in\mathbb R$ the Sobolev (Bessel potential) space is $H^s(E,F)=\{u\in\mathcal S'(E,F):\ (1+|\xi|^2)^{s/2}\widehat u\in L^2\}$, and $\|u\|_{H^s}=\|J^s u\|_{L^2}\in[0,\infty]$, where $J^s$ is the Fourier multiplier with symbol $(1+|\xi|^2)^{s/2}$; by convention $\|u\|_{H^s}=\infty$ when $u\notin H^s$ (definition `SobolevL2.sobolevNorm`).
--
--   Then for every Schwartz function $\varphi\in\mathcal S(E,F)$ and every $s\in\mathbb R$
--   $$\|\varphi\|_{H^s}=\Big(\int_E(1+|\xi|^2)^{s}\,\|\widehat\varphi(\xi)\|_F^2\,d\xi\Big)^{1/2},\qquad \widehat\varphi(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}\varphi(x)\,dx .$$
--   (Every Schwartz function lies in every $H^s$, Mathlib's `SchwartzMap.memSobolev`, so both sides are finite.)
--
--   This is formula (9.1.1.3) of Definition 9.1.1.1 of the source on the test functions, for $G=\mathbb R^n$ and the Sobolev weight $w(\xi)=|\xi|$; together with the density of $C_c^\infty$ in $H^s$ (`SobolevL2.compactSupport_schwartz_dense`) and the completeness of $H^s$ (`SobolevL2.sobolev_complete`) it shows that $H^s$ is the completion of the test functions for this norm, which is how the source defines $H^s_w$. In the paper's normalization (9.1.1.3) the squared norm carries the weight $(1+w^2)^{s/2}$ (not $(1+w^2)^{s}$); for $G=\mathbb R^n$, $\widehat G\cong\mathbb R^n$ and the Sobolev weight $w(\xi)=|\xi|$ (which satisfies (9.1.1.2) with $C_w=1$), the paper's $H^s_w$ is therefore the classical $H^{s/2}$ used here.
--
--   **Formalization Note.** $E$ carries `volume` (Lebesgue measure of the inner product space), tempered distributions are Mathlib's `𝓢'(E, F)`, the Bessel potential is `TemperedDistribution.besselPotential` and membership in $H^s$ is Mathlib's `TemperedDistribution.MemSobolev s 2`. The norm `SobolevL2.sobolevNorm s u : ℝ≥0∞` is $\infty$ off $H^s$, so statements in $[0,\infty]$ cover membership and the norm at once. The Schwartz function is viewed as a tempered distribution through Mathlib's coercion `𝓢(E, F) → 𝓢'(E, F)`, and `𝓕 (φ : E → F)` is the Fourier integral of the underlying function. The right-hand side is a lower Lebesgue integral in $[0,\infty]$ raised to the power $1/2$. Finiteness of both sides (every Schwartz function lies in every $H^s$) is Mathlib's `SchwartzMap.memSobolev` and is not restated here.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 396, Definition 9.1.1.1, (9.1.1.3), specialized to $G=\mathbb R^n$, $w(\xi)=|\xi|$; classical reference: P. Górka and E. G. Reyes, Sobolev spaces on locally compact abelian groups, arXiv:1208.3053v1 (2012), §§1–2, as cited by the paper at Definition 9.1.1.1

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

namespace SobolevL2

/-- For a Schwartz function `φ` and `s : ℝ`,
`‖φ‖_{H^s} = (∫ (1 + ‖ξ‖²)^s ‖𝓕 φ ξ‖² dξ)^{1/2}`, with `𝓕` the Fourier integral
`𝓕 φ ξ = ∫ e^{-2πi⟪x, ξ⟫} φ x dx`. -/
theorem sobolevNorm_schwartz_eq_lintegral_fourier {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (φ : 𝓢(E, F)) :
    sobolevNorm s (φ : 𝓢'(E, F)) =
      (∫⁻ ξ : E, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s) * ‖𝓕 (φ : E → F) ξ‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  sorry

end SobolevL2
