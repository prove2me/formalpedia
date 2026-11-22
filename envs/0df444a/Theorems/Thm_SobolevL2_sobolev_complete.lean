-- Prove2me | Theorems.Thm_SobolevL2_sobolev_complete
-- name    : SobolevL2.sobolev_complete
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:38.805454+00:00
-- url     : https://prove2.me/theorems/2e181a22-b871-47c0-8a7b-45f0d140448b
-- title:
--   Completeness of the Sobolev space $H^s(\mathbb R^n)$: every $\|\cdot\|_{H^s}$-Cauchy sequence in $H^s$ converges in $H^s$
-- statement:
--   **Completeness of $H^s$.** Let $E$ be a finite-dimensional real inner product space (a copy of $\mathbb R^n$, $n=\dim E$) with its Lebesgue measure, let $F$ be a complex Hilbert space (the classical case is $F=\mathbb C$), and let $\mathcal S(E,F)$, $\mathcal S'(E,F)$ be the Schwartz functions and the tempered distributions. The Fourier transform is $\widehat f(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$, extended to $\mathcal S'$ by duality. For $s\in\mathbb R$ the Sobolev (Bessel potential) space is $H^s(E,F)=\{u\in\mathcal S'(E,F):\ (1+|\xi|^2)^{s/2}\widehat u\in L^2\}$, and $\|u\|_{H^s}=\|J^s u\|_{L^2}\in[0,\infty]$, where $J^s$ is the Fourier multiplier with symbol $(1+|\xi|^2)^{s/2}$; by convention $\|u\|_{H^s}=\infty$ when $u\notin H^s$ (definition `SobolevL2.sobolevNorm`).
--
--   Let $s\in\mathbb R$ and let $(u_n)_{n\ge0}$ be a sequence in $H^s(E,F)$ which is Cauchy for the Sobolev norm: for every $\varepsilon>0$ there is $N$ with $\|u_m-u_n\|_{H^s}<\varepsilon$ for all $m,n\ge N$. Then there is $v\in H^s(E,F)$ with
--   $$\|u_n-v\|_{H^s}\longrightarrow0\qquad(n\to\infty).$$
--
--   Together with the inner product $\langle u,v\rangle_{H^s}=\int_E(1+|\xi|^2)^s\langle\widehat u(\xi),\widehat v(\xi)\rangle\,d\xi$ inducing the norm, this is the statement that $H^s(E,F)$ is a Hilbert space, Lemma 9.1.1.2 of the source for $G=\mathbb R^n$ and $w(\xi)=|\xi|$ (the source deduces it from $H^s_w=L^2(\widehat G,(1+w^2)^{s/2}\mu_{\widehat G})$ and [Fol, Prop. 7.9]). In the paper's normalization (9.1.1.3) the squared norm carries the weight $(1+w^2)^{s/2}$ (not $(1+w^2)^{s}$); for $G=\mathbb R^n$, $\widehat G\cong\mathbb R^n$ and the Sobolev weight $w(\xi)=|\xi|$ (which satisfies (9.1.1.2) with $C_w=1$), the paper's $H^s_w$ is therefore the classical $H^{s/2}$ used here.
--
--   **Formalization Note.** $E$ carries `volume` (Lebesgue measure of the inner product space), tempered distributions are Mathlib's `𝓢'(E, F)`, the Bessel potential is `TemperedDistribution.besselPotential` and membership in $H^s$ is Mathlib's `TemperedDistribution.MemSobolev s 2`. The norm `SobolevL2.sobolevNorm s u : ℝ≥0∞` is $\infty$ off $H^s$, so statements in $[0,\infty]$ cover membership and the norm at once. The hypothesis that every $u_n$ lies in $H^s$ (`MemSobolev s 2 (u n)`) is needed because the norm is $\infty$-valued: without it a constant sequence outside $H^s$ would be Cauchy. Convergence is expressed as `sobolevNorm s (u n - v) → 0` in $[0,\infty]$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 396, Lemma 9.1.1.2, specialized to $G=\mathbb R^n$, $w(\xi)=|\xi|$; classical reference: G. B. Folland, Real Analysis. Modern Techniques and Their Applications, Second Edition, John Wiley and Sons, 1999, Prop. 7.9, as cited by the paper in the proof of Lemma 9.1.1.2

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

namespace SobolevL2

/-- `H^s` is complete: a sequence of elements of `H^s` that is Cauchy for `‖·‖_{H^s}` converges in
`‖·‖_{H^s}` to an element of `H^s`. -/
theorem sobolev_complete {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (u : ℕ → 𝓢'(E, F))
    (hu : ∀ n, MemSobolev s 2 (u n))
    (hCauchy : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, sobolevNorm s (u m - u n) < ε) :
    ∃ v : 𝓢'(E, F), MemSobolev s 2 v ∧
      Tendsto (fun n => sobolevNorm s (u n - v)) atTop (𝓝 0) := by
  sorry

end SobolevL2
