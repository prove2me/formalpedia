-- Prove2me | Theorems.Thm_SobolevL2_sobolevNorm_natCast_sq_eq_sum_iteratedLineDeriv
-- name    : SobolevL2.sobolevNorm_natCast_sq_eq_sum_iteratedLineDeriv
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:55.099135+00:00
-- url     : https://prove2.me/theorems/55073a9c-fb77-4df7-9bd8-48aba8a26029
-- title:
--   Integer-order Sobolev norm by derivatives: $\|u\|_{H^k}^2=\sum_{j\le k}\binom kj(2\pi)^{-2j}\sum_{|i|=j}\|\partial_{b_{i_1}}\cdots\partial_{b_{i_j}}u\|_{L^2}^2$
-- statement:
--   **The $H^k$ norm in terms of derivatives.** Let $E$ be a finite-dimensional real inner product space (a copy of $\mathbb R^n$, $n=\dim E$) with its Lebesgue measure, let $F$ be a complex Hilbert space (the classical case is $F=\mathbb C$), and let $\mathcal S(E,F)$, $\mathcal S'(E,F)$ be the Schwartz functions and the tempered distributions. The Fourier transform is $\widehat f(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$, extended to $\mathcal S'$ by duality. For $s\in\mathbb R$ the Sobolev (Bessel potential) space is $H^s(E,F)=\{u\in\mathcal S'(E,F):\ (1+|\xi|^2)^{s/2}\widehat u\in L^2\}$, and $\|u\|_{H^s}=\|J^s u\|_{L^2}\in[0,\infty]$, where $J^s$ is the Fourier multiplier with symbol $(1+|\xi|^2)^{s/2}$; by convention $\|u\|_{H^s}=\infty$ when $u\notin H^s$ (definition `SobolevL2.sobolevNorm`).
--
--   Let $k\ge0$ be an integer and $b=(b_1,\dots,b_n)$ an orthonormal basis of $E$. For $u\in\mathcal S'(E,F)$ and a word $i=(i_1,\dots,i_j)\in\{1,\dots,n\}^j$ write $\partial^{i}_b u=\partial_{b_{i_1}}\cdots\partial_{b_{i_j}}u$, and let $\|w\|_{L^2}=\|w\|_{H^0}\in[0,\infty]$ ($=\infty$ if $w$ is not an $L^2$ function). Then
--   $$\|u\|_{H^k}^2=\sum_{j=0}^{k}\binom{k}{j}\,(2\pi)^{-2j}\sum_{i\in\{1,\dots,n\}^j}\big\|\partial^{i}_b u\big\|_{L^2}^2 ,$$
--   as an identity in $[0,\infty]$. In particular $u\in H^k$ if and only if all $\partial^i_b u$ with $|i|\le k$ are in $L^2$, and $\|u\|_{H^k}$ is equivalent to the classical $W^{k,2}$ norm $\big(\sum_{|\alpha|\le k}\|\partial^\alpha u\|_{L^2}^2\big)^{1/2}$.
--
--   The factor $(2\pi)^{-2j}$ reflects the Fourier convention $\widehat f(\xi)=\int e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$, and the coefficients $\binom kj$ are those of the binomial expansion (9.1.2.8) of the source. It is the quantitative form (equivalence of the norm topology with the topology of the derivative seminorms) of Lemma 9.1.2.2 of the source, in the classical setting of Remark 9.1.2.3 ($G=\mathbb R$, here $\mathbb R^n$); the source's degree $s=2N$ is the classical order $N=k$.
--
--   **Deviation from the source.** The source's inequality (9.1.2.9) compares a quadratic expression with a linear one (erratum I93 of the riemann-masullo formalization, https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md); the exact identity above is the correct classical statement. The source's setting ($\mathbf R_{>0}$-modulated groups, derivatives of the Fourier transform) is replaced by the classical $\mathbb R^n$ case of Remark 9.1.2.3.
--
--   **Formalization Note.** $E$ carries `volume` (Lebesgue measure of the inner product space), tempered distributions are Mathlib's `𝓢'(E, F)`, the Bessel potential is `TemperedDistribution.besselPotential` and membership in $H^s$ is Mathlib's `TemperedDistribution.MemSobolev s 2`. The norm `SobolevL2.sobolevNorm s u : ℝ≥0∞` is $\infty$ off $H^s$, so statements in $[0,\infty]$ cover membership and the norm at once. Words $i$ are functions `Fin j → ι`, the iterated derivative is `∂^{fun l => b (i l)} u` (Mathlib's `LineDeriv.iteratedLineDerivOp` on `𝓢'(E, F)`), squares are taken in $[0,\infty]$, and $(2\pi)^{-2j}$ is `(ENNReal.ofReal (2 * Real.pi) ^ (2 * j))⁻¹`. The sum over words counts each multi-index $\alpha$ with the multiplicity $j!/\alpha!$, which is what makes the identity exact.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 400–401, Lemma 9.1.2.2, (9.1.2.4)–(9.1.2.9), and Remark 9.1.2.3 (the case $G=\mathbb R$), generalized to $\mathbb R^n$

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

namespace SobolevL2

/-- For `k : ℕ` and an orthonormal basis `b` of `E`,
`‖u‖²_{H^k} = ∑_{j=0}^{k} (k choose j) (2π)^{-2j} ∑_{i : Fin j → ι} ‖∂_{b (i 0)} ⋯ ∂_{b (i (j-1))} u‖²_{L²}`,
an identity in `[0, ∞]` (both sides are `∞` unless `u ∈ H^k`). The factors `(2π)^{-2j}` come from
the convention `𝓕 f ξ = ∫ e^{-2πi⟪x, ξ⟫} f x dx`. -/
theorem sobolevNorm_natCast_sq_eq_sum_iteratedLineDeriv {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (k : ℕ) (u : 𝓢'(E, F)) :
    sobolevNorm (k : ℝ) u ^ 2 =
      ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ≥0∞) * (ENNReal.ofReal (2 * Real.pi) ^ (2 * j))⁻¹ *
          ∑ i : Fin j → ι, sobolevNorm 0 (∂^{fun l => b (i l)} u) ^ 2 := by
  sorry

end SobolevL2
