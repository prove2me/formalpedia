-- Prove2me | Theorems.Thm_SobolevL2_compactSupport_schwartz_dense
-- name    : SobolevL2.compactSupport_schwartz_dense
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:44.971031+00:00
-- url     : https://prove2.me/theorems/abaf3775-48a0-47ff-beef-b3721fa99684
-- title:
--   Density of test functions in $H^s(\mathbb R^n)$: compactly supported Schwartz functions are dense in $H^s$ for every real $s$
-- statement:
--   **Density of test functions in $H^s$.** Let $E$ be a finite-dimensional real inner product space (a copy of $\mathbb R^n$, $n=\dim E$) with its Lebesgue measure, let $F$ be a complex Hilbert space (the classical case is $F=\mathbb C$), and let $\mathcal S(E,F)$, $\mathcal S'(E,F)$ be the Schwartz functions and the tempered distributions. The Fourier transform is $\widehat f(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$, extended to $\mathcal S'$ by duality. For $s\in\mathbb R$ the Sobolev (Bessel potential) space is $H^s(E,F)=\{u\in\mathcal S'(E,F):\ (1+|\xi|^2)^{s/2}\widehat u\in L^2\}$, and $\|u\|_{H^s}=\|J^s u\|_{L^2}\in[0,\infty]$, where $J^s$ is the Fourier multiplier with symbol $(1+|\xi|^2)^{s/2}$; by convention $\|u\|_{H^s}=\infty$ when $u\notin H^s$ (definition `SobolevL2.sobolevNorm`).
--
--   For every $s\in\mathbb R$, every $u\in H^s(E,F)$ and every $\varepsilon>0$ there is a smooth compactly supported function $\varphi\in C_c^\infty(E,F)\subset\mathcal S(E,F)$ with
--   $$\|u-\varphi\|_{H^s}<\varepsilon .$$
--   Thus $C_c^\infty(E,F)$, and a fortiori $\mathcal S(E,F)$, is dense in $H^s(E,F)$ for every real $s$, positive or negative.
--
--   In Definition 9.1.1.1 of the source the Sobolev space $H^s_w$ is *defined* as the completion of a space of test functions for the norm (9.1.1.3) (printed as $C_c(\widehat G)$, although (9.1.1.3) takes the Fourier transform of the test function; see erratum I93 of the riemann-masullo formalization, https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md); on $\mathbb R^n$ (with $w(\xi)=|\xi|$) the present density statement, together with completeness (`SobolevL2.sobolev_complete`) and the formula for the norm on test functions (`SobolevL2.sobolevNorm_schwartz_eq_lintegral_fourier`), identifies that completion with the distributional space $H^s$. The proof of Lemma 9.1.1.5 uses the analogous density of $C_c(\widehat G)$ on the Fourier side. In the paper's normalization (9.1.1.3) the squared norm carries the weight $(1+w^2)^{s/2}$ (not $(1+w^2)^{s}$); for $G=\mathbb R^n$, $\widehat G\cong\mathbb R^n$ and the Sobolev weight $w(\xi)=|\xi|$ (which satisfies (9.1.1.2) with $C_w=1$), the paper's $H^s_w$ is therefore the classical $H^{s/2}$ used here.
--
--   **Formalization Note.** $E$ carries `volume` (Lebesgue measure of the inner product space), tempered distributions are Mathlib's `𝓢'(E, F)`, the Bessel potential is `TemperedDistribution.besselPotential` and membership in $H^s$ is Mathlib's `TemperedDistribution.MemSobolev s 2`. The norm `SobolevL2.sobolevNorm s u : ℝ≥0∞` is $\infty$ off $H^s$, so statements in $[0,\infty]$ cover membership and the norm at once. Test functions are Schwartz maps `φ : 𝓢(E, F)` with `HasCompactSupport (φ : E → F)` (a Schwartz map is smooth, so these are exactly the $C_c^\infty$ functions), embedded in `𝓢'(E, F)` by Mathlib's coercion. The approximation is in the $[0,\infty]$-valued norm with $\varepsilon\in(0,\infty]$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 396, Definition 9.1.1.1 ($H^s_w$ as a completion of test functions) (cf. p. 399, proof of Lemma 9.1.1.5, which uses the analogous density of $C_c(\widehat G)$ on the Fourier side), specialized to $G=\mathbb R^n$, $w(\xi)=|\xi|$; classical reference: P. Górka and E. G. Reyes, Sobolev spaces on locally compact abelian groups, arXiv:1208.3053v1 (2012), §§1–2, as cited by the paper at Definition 9.1.1.1

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

namespace SobolevL2

/-- For every real `s`, compactly supported smooth (Schwartz) functions are dense in `H^s`: every
`u ∈ H^s` is approximated in `‖·‖_{H^s}` by some `φ ∈ 𝓢(E, F)` with compact support. -/
theorem compactSupport_schwartz_dense {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (u : 𝓢'(E, F)) (hu : MemSobolev s 2 u)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ φ : 𝓢(E, F), HasCompactSupport (φ : E → F) ∧
      sobolevNorm s (u - (φ : 𝓢'(E, F))) < ε := by
  sorry

end SobolevL2
