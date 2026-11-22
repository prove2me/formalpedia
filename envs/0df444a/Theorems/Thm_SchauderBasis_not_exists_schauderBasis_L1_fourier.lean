-- Prove2me | Theorems.Thm_SchauderBasis_not_exists_schauderBasis_L1_fourier
-- name    : SchauderBasis.not_exists_schauderBasis_L1_fourier
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:54.319804+00:00
-- url     : https://prove2.me/theorems/ec369d6e-7d99-4fe4-ada5-ee2c790ed5d6
-- title:
--   The exponential system, in the order $0,1,-1,2,-2,\dots$, is not a Schauder basis of $L^1(\mathbb T)$ (Fourier series need not converge in $L^1$-norm)
-- statement:
--   **The exponential system, in its standard order, is not a Schauder basis of $L^1(\mathbb T)$.** Let $T>0$, let $\mathbb T=\mathbb R/T\mathbb Z$ carry its normalized Haar measure, and $e_n(x)=e^{2\pi inx/T}$ for $n\in\mathbb Z$. Order $\mathbb Z$ in the standard way $0,1,-1,2,-2,\dots$, i.e. $\zeta(0)=0$, $\zeta(2j-1)=j$, $\zeta(2j)=-j$ for $j\ge1$; for this enumeration the partial sums of odd length $2N+1$ are the symmetric Fourier partial sums $S_Nf=\sum_{|n|\le N}\widehat f(n)e_n$. Then there is **no** Schauder basis of the Banach space $L^1(\mathbb T)$ whose $n$-th vector is (the class of) $e_{\zeta(n)}$ for every $n\ge0$.
--
--   Since the Fourier coefficients are continuous functionals on $L^1(\mathbb T)$ and would have to be the coefficient functionals, this says that there is $f\in L^1(\mathbb T)$ whose Fourier series does not converge to $f$ in $L^1$-norm. The paper (pp. 157–158) gives $L^1(\mathbb T)$ as the second example of a normed completion of $C^\infty(\mathbb T)$ in which the exponential system is not a Schauder basis although its coefficient functionals remain continuous, and refers to Kolmogorov's example of a divergent Fourier–Lebesgue series.
--
--   **Formalization Note.** Mathlib's `SchauderBasis ℂ (Lp ℂ 1 haarAddCircle)` and `fourierLp 1 n`. The circle has an arbitrary period $T>0$ (the paper takes $T=1$). The paper does not fix an enumeration of $\mathbb Z$; the standard one is used.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 157–158, §4.1.1 (the exponential system in $L^1(\mathbb T)$; the paper refers here to A. Kolmogorov, Une série de Fourier-Lebesgue divergente partout, C. R. Acad. Sci. Paris 183 (1926), pp. 1327–1328)

import Mathlib

open Filter Topology MeasureTheory AddCircle ENNReal

set_option autoImplicit false

namespace SchauderBasis

theorem not_exists_schauderBasis_L1_fourier (T : ℝ) [Fact (0 < T)] :
    ¬ ∃ b : SchauderBasis ℂ (Lp ℂ 1 (haarAddCircle (T := T))),
      ∀ n : ℕ, b.basis n = fourierLp (T := T) 1 (if Odd n then (((n + 1) / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) := by sorry

end SchauderBasis
