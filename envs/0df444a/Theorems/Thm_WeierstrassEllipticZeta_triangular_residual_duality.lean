-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_residual_duality
-- name    : WeierstrassEllipticZeta.triangular_residual_duality
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T11:58:21.292014+00:00
-- url     : https://prove2.me/theorems/ee4050b8-49f2-4708-92ce-a8cb556a4126
-- title:
--   Residual duality in a time-polynomial presentation
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$ and fix polynomials $r_1,r_2,r_3\in\mathbb C[T]$. Define the substitution
--
--   $$\Phi:A\longrightarrow\mathbb C[T],\qquad
--   \Phi(t)=T,\quad \Phi(x_i)=r_i(T).$$
--
--   Let $M\in\mathbb C[T]$ be nonzero and let $I\subseteq A$ be an ideal such that
--
--   $$f\in I\quad\Longleftrightarrow\quad M\mid\Phi(f)\qquad(f\in A).$$
--
--   For any polynomial $p\in A$, form the hypersurface intersection and its residual ideal
--
--   $$J=I+(p),\qquad R=I:p=\{f\in A:fp\in I\}.$$
--
--   For an ideal $K\subseteq A$, write $I:K=\{f\in A:fK\subseteq I\}$. Then $J$ and $R$ are mutual residuals:
--
--   $$I:R=J,\qquad I:J=R.$$
--
--   In particular,
--
--   $$I:(I:p)=I+(p).$$
--
--   Thus taking the residual of the hypersurface intersection and then taking its residual again recovers the intersection. Equivalently, the images of $J$ and $R$ in $A/I$ are mutual annihilators.
--
--   **Formalization Note** The exact membership presentation and $M\ne0$ are explicit hypotheses. No monicity, contact, lattice, nonsingularity or separate finite-dimensionality hypothesis is imposed. The formal conclusion consists of the two displayed ideal equalities; the annihilator wording is their quotient-ring interpretation. The first residual is by the singleton polynomial $p$, while the two colons in the conclusion are by the full underlying sets of the ideals $R$ and $J$. The theorem allows $p=0$, $\Phi(p)=0$ and nonzero constant $M$. It does not assert that these ideals are principal in the four-variable ring, nor does it prove a global zero estimate.
-- source:
--   Derived residual-duality calculation for the finite-intersection algebra approach associated with Senthil Kumar K (2026), Appendix A, https://doi.org/10.1017/S001309152610145X. This exact algebraic statement is proved here, not quoted from the article. The Proved triangular_residual_quotient_length theorem identifies I:p with divisibility by G=M/gcd(M,Phi(p)). Testing the second colon on the time lift of G and cancelling its nonzero factor forces divisibility by the gcd; a lifted polynomial Bezout identity then gives membership in I+(p). The reverse colon equality follows directly from ideal sums. Primary formal references: Submodule.mem_colon, Submodule.mem_colon_singleton, exists_gcd_eq_mul_add_mul, EuclideanDomain.mul_div_cancel', mul_dvd_mul_iff_right and Submodule.mem_sup.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Colon

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_residual_duality
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ p : MvPolynomial (Fin 4) ℂ,
      let J := I ⊔ Ideal.span {p}
      let R := I.colon {p}
      I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
      I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) = R := by sorry
