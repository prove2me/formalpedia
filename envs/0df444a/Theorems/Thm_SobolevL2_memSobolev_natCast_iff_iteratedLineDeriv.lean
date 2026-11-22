-- Prove2me | Theorems.Thm_SobolevL2_memSobolev_natCast_iff_iteratedLineDeriv
-- name    : SobolevL2.memSobolev_natCast_iff_iteratedLineDeriv
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:55.313624+00:00
-- url     : https://prove2.me/theorems/03dae4d7-9f0f-43a2-b02d-4028ea6ef278
-- title:
--   Characterization of $H^k(\mathbb R^n)$, $k\in\mathbb N$, by derivatives: $u\in H^k$ iff all distributional derivatives of order $\le k$ of $u$ are $L^2$ functions
-- statement:
--   **$H^k=W^{k,2}$: the Sobolev space of integer order via derivatives.** Let $E$ be a finite-dimensional real inner product space (a copy of $\mathbb R^n$, $n=\dim E$) with its Lebesgue measure, let $F$ be a complex Hilbert space (the classical case is $F=\mathbb C$), and let $\mathcal S(E,F)$, $\mathcal S'(E,F)$ be the Schwartz functions and the tempered distributions. The Fourier transform is $\widehat f(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$, extended to $\mathcal S'$ by duality. For $s\in\mathbb R$ the Sobolev (Bessel potential) space is $H^s(E,F)=\{u\in\mathcal S'(E,F):\ (1+|\xi|^2)^{s/2}\widehat u\in L^2\}$, and $\|u\|_{H^s}=\|J^s u\|_{L^2}\in[0,\infty]$, where $J^s$ is the Fourier multiplier with symbol $(1+|\xi|^2)^{s/2}$; by convention $\|u\|_{H^s}=\infty$ when $u\notin H^s$ (definition `SobolevL2.sobolevNorm`).
--
--   For a tempered distribution $u$ and directions $m_1,\dots,m_j\in E$ write $\partial_{m_1}\cdots\partial_{m_j}u$ for the iterated distributional directional derivative. Then for every integer $k\ge0$,
--   $$u\in H^k(E,F)\iff \partial_{m_1}\cdots\partial_{m_j}u\in L^2(E,F)\ \text{ for all } 0\le j\le k \text{ and all } m_1,\dots,m_j\in E .$$
--   (For $j=0$ the condition is $u\in L^2$.) In coordinates: $u\in H^k(\mathbb R^n)$ if and only if $\partial^\alpha u\in L^2$ for every multi-index $|\alpha|\le k$, i.e. $H^k=W^{k,2}$.
--
--   This is the qualitative content of Lemma 9.1.2.2 of the source (for $s=2N$ the Sobolev topology is given by the seminorms $\|D^k\widehat f\|_{L^2}$, $0\le k\le N$) in the classical setting singled out in Remark 9.1.2.3, $G=\mathbb R$ (here $\mathbb R^n$), where these seminorms are the classical Sobolev seminorms $\|\partial_x^k\widehat f\|_{L^2}$ of the function $\widehat f$ on $\widehat G\cong\mathbb R$ (the distribution $u$ of the present statement plays the role of $\widehat f$). The norm identity is `SobolevL2.sobolevNorm_natCast_sq_eq_sum_iteratedLineDeriv`. The source's degree $s=2N$ corresponds to the classical order $N$ used here.
--
--   **Deviation from the source.** The source works on $\mathbf R_{>0}$-modulated groups, with a weight on the group and derivatives of the Fourier transform; Remark 9.1.2.3 states the classical case $G=\mathbb R$ with derivatives of $f$ itself. Remark 9.1.2.3 prints $\|f\|_{s,k,2}=\|\partial_x^kf\|_{L^2}$, whereas (9.1.2.5) differentiates $\widehat f$, so $\widehat f$ must replace $f$ there (erratum I93 of the riemann-masullo formalization, https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md); the classical statement on $\mathbb R^n$ is formalized.
--
--   **Formalization Note.** $E$ carries `volume` (Lebesgue measure of the inner product space), tempered distributions are Mathlib's `𝓢'(E, F)`, the Bessel potential is `TemperedDistribution.besselPotential` and membership in $H^s$ is Mathlib's `TemperedDistribution.MemSobolev s 2`. The norm `SobolevL2.sobolevNorm s u : ℝ≥0∞` is $\infty$ off $H^s$, so statements in $[0,\infty]$ cover membership and the norm at once. The iterated derivative is Mathlib's `LineDeriv.iteratedLineDerivOp` (notation `∂^{m}` for `m : Fin j → E`) on `𝓢'(E, F)`; "is an $L^2$ function" is `MemSobolev 0 2`, which by `TemperedDistribution.memSobolev_zero_iff` means being represented by an element of `Lp F 2 volume`. All directions $m_i\in E$ are allowed; by multilinearity it is equivalent to use the vectors of a basis.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 400–401, Lemma 9.1.2.2, (9.1.2.4)–(9.1.2.5), and Remark 9.1.2.3 (the case $G=\mathbb R$), generalized to $\mathbb R^n$

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

namespace SobolevL2

/-- For a natural number `k`, a tempered distribution lies in `H^k` if and only if all its
distributional (iterated directional) derivatives `∂_{m₁} ⋯ ∂_{mⱼ} u` of order `j ≤ k` are `L²`
functions. -/
theorem memSobolev_natCast_iff_iteratedLineDeriv {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (k : ℕ) (u : 𝓢'(E, F)) :
    MemSobolev (k : ℝ) 2 u ↔ ∀ j ≤ k, ∀ m : Fin j → E, MemSobolev 0 2 (∂^{m} u) := by
  sorry

end SobolevL2
