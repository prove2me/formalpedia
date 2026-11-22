-- Prove2me | Theorems.Thm_SchauderBasis_not_exists_schauderBasis_continuousMap_fourier
-- name    : SchauderBasis.not_exists_schauderBasis_continuousMap_fourier
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:53.481516+00:00
-- url     : https://prove2.me/theorems/85ba9650-cc40-4242-9c09-0e66afdd9f33
-- title:
--   The exponential system, in the order $0,1,-1,2,-2,\dots$, is not a Schauder basis of $C(\mathbb T)$ (Fourier series of continuous functions need not converge uniformly)
-- statement:
--   **The exponential system, in its standard order, is not a Schauder basis of $C(\mathbb T)$.** Let $T>0$, $\mathbb T=\mathbb R/T\mathbb Z$, let $C(\mathbb T)$ be the Banach space of continuous complex-valued functions on $\mathbb T$ with the uniform norm, and $e_n(x)=e^{2\pi inx/T}$ for $n\in\mathbb Z$. Order $\mathbb Z$ in the standard way $0,1,-1,2,-2,\dots$, i.e. $\zeta(0)=0$, $\zeta(2j-1)=j$, $\zeta(2j)=-j$ for $j\ge1$; for this enumeration the partial sums of odd length $2N+1$ are the symmetric Fourier partial sums $S_Nf=\sum_{|n|\le N}\widehat f(n)e_n$. Then there is **no** Schauder basis of $C(\mathbb T)$ whose $n$-th vector is $e_{\zeta(n)}$ for every $n\ge0$.
--
--   Since the Fourier coefficients are continuous functionals on $C(\mathbb T)$ and would have to be the coefficient functionals, this says that there is a continuous function whose Fourier series does not converge uniformly. The paper (pp. 157–158) gives $C(\mathbb T)$ as an example of a normed completion of $C^\infty(\mathbb T)$ in which the exponential system is not a Schauder basis although its coefficient functionals remain continuous.
--
--   **Formalization Note.** Mathlib's `SchauderBasis ℂ C(AddCircle T, ℂ)` (sup norm, convergence of the partial sums over `Finset.range N`) and `fourier n : C(AddCircle T, ℂ)`. The circle has an arbitrary period $T>0$ (the paper takes $T=1$). The paper does not fix an enumeration of $\mathbb Z$; the standard one is used (whether the exponential system fails to be a basis of $C(\mathbb T)$ in every enumeration is a deeper question and is not claimed).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 157–158, §4.1.1 (the exponential system in $C(\mathbb T)$); classical reference: Y. Katznelson, An Introduction to Harmonic Analysis, 3rd ed., Cambridge University Press, 2012, Ch. II, §1.3, p. 57 (as cited by the paper)

import Mathlib

open Filter Topology MeasureTheory AddCircle ENNReal

set_option autoImplicit false

namespace SchauderBasis

theorem not_exists_schauderBasis_continuousMap_fourier (T : ℝ) [Fact (0 < T)] :
    ¬ ∃ b : SchauderBasis ℂ C(AddCircle T, ℂ),
      ∀ n : ℕ, b.basis n = fourier (T := T) (if Odd n then (((n + 1) / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) := by sorry

end SchauderBasis
