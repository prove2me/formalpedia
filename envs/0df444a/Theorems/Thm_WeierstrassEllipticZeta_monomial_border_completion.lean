-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_monomial_border_completion
-- name    : WeierstrassEllipticZeta.monomial_border_completion
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T02:17:56.980169+00:00
-- url     : https://prove2.me/theorems/ae075fed-413a-4d6c-9026-09478fdf1bc0
-- title:
--   Completing monomial boundary relations for every ideal
-- statement:
--   Let $K$ be a field and let $\sigma$ be a finite set of variables. For a finite exponent set $S\subset\mathbb N^{\sigma}$, define its monomial boundary by
--   $$ B=\{d+e_i:d\in S,\ i\in\sigma\}\setminus S, $$
--   where $e_i$ is the exponent of coordinate $X_i$.
--
--   For each $a\in B$, let $b_a\in K[\sigma]$ have monomial support contained in $S$. Then there are polynomials $r_{i,d}$, for coordinates $i$ and exponents $d\in S$, each supported in $S$, such that for every ideal $I\subseteq K[\sigma]$,
--   $$
--   \bigl(\forall a\in B,\ X^a-b_a\in I\bigr)
--   \quad\Longleftrightarrow\quad
--   \bigl(\forall i\in\sigma,\ \forall d\in S,\ X_iX^d-r_{i,d}\in I\bigr).
--   $$
--   The same family $r_{i,d}$ works for every ideal $I$. The set $S$ may be empty and need not be closed under taking monomial divisors.
-- source:
--   Derived monomial-boundary completion for the frontier https://prove2.me/theorems/27b4055a-78d2-4844-86a1-29fa1008c8d7. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting result completes boundary relations to all coordinate products and proves equivalence of ideal containment in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The uniform geometric construction remains open.

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Finset.Union

noncomputable section

theorem WeierstrassEllipticZeta.monomial_border_completion
    (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ]
    (S : Finset (σ →₀ ℕ)) (b : (σ →₀ ℕ) → MvPolynomial σ K) :
    let B := (Finset.univ.biUnion fun i : σ =>
      S.image (fun d => d + Finsupp.single i 1)) \ S
    (∀ e ∈ B, (b e).support ⊆ S) →
    ∃ r : σ → (σ →₀ ℕ) → MvPolynomial σ K,
      (∀ i : σ, ∀ d ∈ S, (r i d).support ⊆ S) ∧
      ∀ I : Ideal (MvPolynomial σ K),
        (∀ e ∈ B, MvPolynomial.monomial e 1 - b e ∈ I) ↔
          ∀ i : σ, ∀ d ∈ S,
            MvPolynomial.X i * MvPolynomial.monomial d 1 - r i d ∈ I := by sorry
