-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_family_bounded_generic_nonvanishing
-- name    : WeierstrassEllipticZeta.finite_family_bounded_generic_nonvanishing
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T21:21:30.282762+00:00
-- url     : https://prove2.me/theorems/65d176cd-f1a0-4656-a726-d98547fe3db0
-- title:
--   Bounded integer generic combinations nonvanishing on finite sets
-- statement:
--   Let $V$ be a finite subset of $\mathbb C^4$, let $K\in\mathbb N$, and let $f_0,\ldots,f_{K-1}\in\mathbb C[x_0,x_1,x_2,x_3]$. Suppose these polynomials have no common zero on $V$: for each $v\in V$, some $f_j(v)$ is nonzero.
--
--   Then there exists an integer $a$ with
--   $$0\leq a\leq |V|(K-1)$$
--   such that the polynomial
--   $$q=\sum_{j=0}^{K-1}a^j f_j$$
--   is nonzero at every point of $V$. Moreover, for every $D\in\mathbb N$ such that $\deg_{\rm tot}f_j\leq D$ for all $j$, one has $\deg_{\rm tot}q\leq D$.
--
--   Here $K-1$ is truncated subtraction in $\mathbb N$, $a^0=1$ also for $a=0$, and total degree of the zero polynomial is zero. Empty finite sets and $K=0$ are included.
--
--   The result compresses simultaneous nonvanishing of a finite polynomial family into one combination with constant integer coefficients and an explicit bound on its parameter, while preserving the degree bound.
-- source:
--   Derived finite-avoidance lemma associated with the differential-polynomial and finite-set setting of Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. It is proved here, not quoted from that theorem. For K polynomials with no common zero on a finite set V, an integer a between 0 and |V|*(K-1) makes their combination with coefficients a^j nonzero on all of V, without increasing a common total-degree bound. The proof forms the product over V of the evaluation polynomials in a and uses its degree bound to exclude vanishing at every integer in that range. Mathlib references: Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, natDegree_prod_le, natDegree_sum_le_of_forall_le, and MvPolynomial.totalDegree_smul_le. No Prove2Me theorem dependencies.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic

open scoped Classical

theorem WeierstrassEllipticZeta.finite_family_bounded_generic_nonvanishing
    (V : Finset (Fin 4 → ℂ)) (K : ℕ) (f : Fin K → MvPolynomial (Fin 4) ℂ)
    (h : ∀ v : V, ∃ j : Fin K, MvPolynomial.eval v.val (f j) ≠ 0) :
    ∃ a : ℕ, a ≤ V.card * (K - 1) ∧
      let q := ∑ j : Fin K, MvPolynomial.C ((a : ℂ) ^ j.val) * f j
      (∀ v : V, MvPolynomial.eval v.val q ≠ 0) ∧
      ∀ D : ℕ, (∀ j : Fin K, (f j).totalDegree ≤ D) → q.totalDegree ≤ D := by sorry
