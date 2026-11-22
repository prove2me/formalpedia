-- Prove2me | Theorems.Thm_SchauderBasis_exists_schauderBasis_Lp_fourier
-- name    : SchauderBasis.exists_schauderBasis_Lp_fourier
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:53.916112+00:00
-- url     : https://prove2.me/theorems/51be460a-9034-426a-8796-972bc49d1a1c
-- title:
--   M. Riesz: the exponential system $e_n(x)=e^{2\pi inx/T}$, in the order $n=0,1,-1,2,-2,\dots$, is a Schauder basis of $L^p(\mathbb T)$ for $1<p<\infty$
-- statement:
--   **M. Riesz: the exponential system, in its standard order, is a Schauder basis of $L^p(\mathbb T)$, $1<p<\infty$.** Let $T>0$, let $\mathbb T=\mathbb R/T\mathbb Z$ carry its normalized Haar measure, and let $e_n(x)=e^{2\pi inx/T}$ for $n\in\mathbb Z$. Order $\mathbb Z$ in the standard way $0,1,-1,2,-2,\dots$, i.e. $\zeta(0)=0$, $\zeta(2j-1)=j$, $\zeta(2j)=-j$ for $j\ge1$; for this enumeration the partial sums of odd length $2N+1$ are the symmetric Fourier partial sums $S_Nf=\sum_{|n|\le N}\widehat f(n)e_n$. Then for every real $1<p<\infty$ the sequence $(e_{\zeta(n)})_{n\ge0}$ is a Schauder basis of the Banach space $L^p(\mathbb T)$: there are continuous linear functionals $e_n^*$ on $L^p(\mathbb T)$ with $e_n^*(e_{\zeta(k)})=\delta_{n,k}$ and
--   $$f=\lim_{N\to\infty}\sum_{n<N}e_n^*(f)\,e_{\zeta(n)}\quad\text{in }L^p(\mathbb T)\qquad(f\in L^p(\mathbb T)).$$
--   Necessarily $e_n^*(f)=\widehat f(\zeta(n))$ is a Fourier coefficient, so the statement is equivalent to M. Riesz's theorem that the Fourier series of every $f\in L^p(\mathbb T)$, $1<p<\infty$, converges to $f$ in $L^p$-norm. The order matters: for $p\neq2$ the exponential system is not an unconditional basis of $L^p(\mathbb T)$.
--
--   The paper recalls this (p. 157) in contrast with $C(\mathbb T)$ and $L^1(\mathbb T)$, where the exponential system is not a Schauder basis.
--
--   **Formalization Note.** Mathlib's `SchauderBasis ℂ (Lp ℂ p haarAddCircle)` (convergence of the partial sums over `Finset.range N`); `fourierLp p n` is the class of $e_n$ in $L^p$. The circle has an arbitrary period $T>0$ (the paper takes $T=1$). The instance `[Fact (1 ≤ p)]` is required for `Lp` to be a normed space and is implied by `1 < p`; `p ≠ ∞` excludes $p=\infty$. The paper does not fix an enumeration of $\mathbb Z$; the standard one is used.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 157, §4.1.1 (the exponential system in $L^p(\mathbb T)$); classical reference: Y. Katznelson, An Introduction to Harmonic Analysis, 3rd ed., Cambridge University Press, 2012, Ch. II, §1.5, Theorem, p. 59 (as cited by the paper)

import Mathlib

open Filter Topology MeasureTheory AddCircle ENNReal

set_option autoImplicit false

namespace SchauderBasis

theorem exists_schauderBasis_Lp_fourier (T : ℝ) [Fact (0 < T)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p) (hp' : p ≠ ∞) :
    ∃ b : SchauderBasis ℂ (Lp ℂ p (haarAddCircle (T := T))),
      ∀ n : ℕ, b.basis n = fourierLp (T := T) p (if Odd n then (((n + 1) / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) := by sorry

end SchauderBasis
