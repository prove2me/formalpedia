-- Prove2me | Theorems.Thm_SobolevL2_sobolevNorm_neg_eq_dual_norm
-- name    : SobolevL2.sobolevNorm_neg_eq_dual_norm
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:50.538596+00:00
-- url     : https://prove2.me/theorems/bf5d37f6-9d93-4bd3-91ed-1f625b306093
-- title:
--   Duality $H^{-s}=(H^s)'$: $\|v\|_{H^{-s}}=\sup\{|v(\varphi)|:\ \varphi\in\mathcal S,\ \|\varphi\|_{H^s}\le1\}$ for every tempered distribution $v$
-- statement:
--   **Duality between $H^s$ and $H^{-s}$.** Let $E$ be a finite-dimensional real inner product space (a copy of $\mathbb R^n$) with Lebesgue measure, $\mathcal S(E)=\mathcal S(E,\mathbb C)$ the Schwartz space and $\mathcal S'(E)$ the scalar tempered distributions, with the Fourier transform $\widehat f(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$. For $s\in\mathbb R$ let $\|u\|_{H^s}=\|(1+|\xi|^2)^{s/2}\widehat u\|_{L^2}\in[0,\infty]$ ($=\infty$ when $u\notin H^s$).
--
--   Then for every $s\in\mathbb R$ and every $v\in\mathcal S'(E)$,
--   $$\|v\|_{H^{-s}}=\sup\big\{|v(\varphi)|:\ \varphi\in\mathcal S(E),\ \|\varphi\|_{H^s}\le1\big\}\in[0,\infty].$$
--   Equivalently: a tempered distribution $v$ belongs to $H^{-s}$ if and only if $|v(\varphi)|\le C\|\varphi\|_{H^s}$ for all Schwartz $\varphi$, and then the smallest such $C$ is $\|v\|_{H^{-s}}$. Since $\mathcal S$ is dense in $H^s$, this says that the bilinear pairing $\langle\varphi,\psi\rangle=\int_E\varphi\psi\,dx$ on Schwartz functions extends to a continuous pairing $H^s\times H^{-s}\to\mathbb C$ which induces an isometric isomorphism of $H^{-s}$ onto the dual Banach space $(H^s)'$.
--
--   This is Lemma 9.1.1.5 of the source ((9.1.1.9)–(9.1.1.12): the pairing $\int\phi\psi$ extends to a continuous non-degenerate bilinear form $H^s_w\times H^{-s}_w\to\mathbb C$ inducing an isometry $(H^s_w)'_\beta\to H^{-s}_w$) for $G=\mathbb R^n$ and $w(\xi)=|\xi|$; the source deduces it from the duality of $L^2$ spaces [Fol, Thm. 6.15, Prop. 6.13]. In the paper's normalization (9.1.1.3) the squared norm carries the weight $(1+w^2)^{s/2}$ (not $(1+w^2)^{s}$); for $G=\mathbb R^n$, $\widehat G\cong\mathbb R^n$ and the Sobolev weight $w(\xi)=|\xi|$ (which satisfies (9.1.1.2) with $C_w=1$), the paper's $H^s_w$ is therefore the classical $H^{s/2}$ used here.
--
--   The source's pairing (9.1.1.10) is $\int_{\widehat G}\phi\psi\,d\mu_{\widehat G}$ between functions on the dual group; for $G=\mathbb R^n$ it corresponds, through the Fourier transform, to the pairing $v(\varphi)$ used here composed with the reflection $x\mapsto-x$, an isometry of every $H^s$, so the dual-norm identity is the same for both pairings.
--
--   **Deviation from the source.** The source states the lemma for $s\ge0$; the classical statement holds for all real $s$, and is formalized for all $s$. The bound (9.1.1.15) in the source carries spurious square roots on the $L^2$ norms (erratum I93 of the riemann-masullo formalization, https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md); the correct Cauchy–Schwarz bound $|v(\varphi)|\le\|v\|_{H^{-s}}\,\|\varphi\|_{H^s}$ for $\varphi\in\mathcal S(E)$ is the half $\sup\{|v(\varphi)|:\|\varphi\|_{H^s}\le1\}\le\|v\|_{H^{-s}}$ of the formula above.
--
--   **Formalization Note.** $\mathbb R^n$ is a finite-dimensional real inner product space `E` with `volume`; `v : 𝓢'(E, ℂ)` is applied to Schwartz functions `φ : 𝓢(E, ℂ)` (Mathlib's pairing `v φ`, which for an integrable function $g$ is $\int\varphi g\,dx$, bilinear and without complex conjugation). The norms are `SobolevL2.sobolevNorm` (values in $[0,\infty]$), and the supremum is over Schwartz functions of $H^s$ norm at most $1$ of $\|v(\varphi)\|$ in $[0,\infty]$. Both sides are $\infty$ exactly when $v\notin H^{-s}$. The scalar case $F=\mathbb C$ is essential (for vector-valued distributions the analogous supremum is a different norm).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 397–399, Lemma 9.1.1.5, (9.1.1.9)–(9.1.1.12), specialized to $G=\mathbb R^n$, $w(\xi)=|\xi|$; classical reference: G. B. Folland, Real Analysis. Modern Techniques and Their Applications, Second Edition, John Wiley and Sons, 1999, Thm. 6.15 and Prop. 6.13 (duality of $L^2$), as cited by the paper in the proof of Lemma 9.1.1.5

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

namespace SobolevL2

/-- `H^{-s}` is the dual of `H^s` for the bilinear pairing extending `∫ φ ψ`: for every scalar
tempered distribution `v`, its `H^{-s}` norm equals the norm of the functional `φ ↦ v φ` on Schwartz
functions measured in the `H^s` norm (both sides being `∞` exactly when `v ∉ H^{-s}`). -/
theorem sobolevNorm_neg_eq_dual_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (s : ℝ) (v : 𝓢'(E, ℂ)) :
    sobolevNorm (-s) v =
      ⨆ (φ : 𝓢(E, ℂ)) (_ : sobolevNorm s (φ : 𝓢'(E, ℂ)) ≤ 1), ‖v φ‖ₑ := by
  sorry

end SobolevL2
