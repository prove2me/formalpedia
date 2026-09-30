-- Prove2me | Theorems.Thm_TranscendenceTheory_bihomogeneous_lift_four_variables
-- name    : TranscendenceTheory.bihomogeneous_lift_four_variables
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T13:52:38.836386+00:00
-- url     : https://prove2.me/theorems/b8e5a796-1f3a-4235-98dc-aee0ef1a5c98
-- title:
--   Bihomogeneous lift of a polynomial with two degree bounds
-- statement:
--   Let $R$ be a commutative semiring, and let $P\in R[Z_0,Z_1,Z_2,Z_3]$. Let $m,n\ge0$ be integers such that every exponent vector $d$ of a monomial with nonzero coefficient in $P$ satisfies
--
--   $$d_0\le m,\qquad d_1+d_2+d_3\le n.$$
--
--   There exists a polynomial $Q\in R[Y_0,Y_1,X_0,X_1,X_2,X_3,X_4]$ such that every supported exponent vector $e$, in this displayed variable order, satisfies
--
--   $$e_0+e_1=m,\qquad e_2+e_3+e_4+e_5+e_6=n,\qquad e_6=0,$$
--
--   and for all $x_0,x_1,x_2,x_3,r,s,t\in R$,
--
--   $$Q(r,rx_0;s,sx_1,sx_2,sx_3,t)=r^m s^n P(x_0,x_1,x_2,x_3).$$
--
--   Thus $Q$ is bihomogeneous of the prescribed degrees $m,n$, is independent of $X_4$, and has the expected scaling and dehomogenization identity. No field, domain, nonzero-polynomial or nonzero-scalar assumption is required. In particular $r,s$ may be zero and $m,n$ may be zero.
--
--   An explicit construction replaces each monomial $c_d Z_0^{d_0}Z_1^{d_1}Z_2^{d_2}Z_3^{d_3}$ by
--
--   $$c_dY_0^{m-d_0}Y_1^{d_0}X_0^{n-d_1-d_2-d_3}X_1^{d_1}X_2^{d_2}X_3^{d_3}.$$
--
--   The padding exponents are nonnegative by the hypotheses. The identity is polynomial and uses no division.
-- source:
--   Bihomogenization step in Senthil Kumar K (2026), proof of Lemma 9 and Appendix equations (A.8)-(A.9), https://doi.org/10.1017/S001309152610145X. This derived algebraic formulation proves monomial padding and the scaling identity over any commutative semiring, using a bound on combined degree in the last three affine variables. The source uses complex coefficients and division notation; the formalization uses a polynomial identity valid even at zero scaling factors. The extra fifth elliptic projective variable is unused by the constructed lift.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation

theorem TranscendenceTheory.bihomogeneous_lift_four_variables (R : Type*) [CommSemiring R]
    (P : MvPolynomial (Fin 4) R) (m n : ℕ)
    (hP : ∀ d ∈ P.support, d 0 ≤ m ∧ d 1 + d 2 + d 3 ≤ n) :
    ∃ Q : MvPolynomial (Fin 7) R,
      (∀ d ∈ Q.support, d 0 + d 1 = m ∧
        d 2 + d 3 + d 4 + d 5 + d 6 = n ∧ d 6 = 0) ∧
      ∀ (x : Fin 4 → R) (r s t : R),
        MvPolynomial.eval ![r, r * x 0, s, s * x 1, s * x 2, s * x 3, t] Q =
          r ^ m * s ^ n * MvPolynomial.eval x P := by sorry
