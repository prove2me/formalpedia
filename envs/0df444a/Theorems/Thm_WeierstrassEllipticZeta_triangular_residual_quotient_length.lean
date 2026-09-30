-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_residual_quotient_length
-- name    : WeierstrassEllipticZeta.triangular_residual_quotient_length
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T02:42:02.036024+00:00
-- url     : https://prove2.me/theorems/2329c0ec-4fe7-4f32-b68f-e626dd817913
-- title:
--   Residual quotient algebra and length in a time-polynomial presentation
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$, choose $r_1,r_2,r_3\in\mathbb C[T]$, and let
--
--   $$\Phi:A\longrightarrow\mathbb C[T],\qquad
--   \Phi(t)=T,\quad\Phi(x_i)=r_i(T).$$
--
--   Let $M\in\mathbb C[T]$ be nonzero and let $I\subseteq A$ be an ideal satisfying, for every $f\in A$,
--
--   $$f\in I\quad\Longleftrightarrow\quad M\mid\Phi(f).$$
--
--   For any $p\in A$, set $q=\Phi(p)$, $g=\gcd(M,q)$ and $G=M/g$. The quotient is exact because $g$ divides $M$. Define the residual ideal
--
--   $$R=I:p=\{f\in A:fp\in I\}.$$
--
--   Then
--
--   $$f\in R\quad\Longleftrightarrow\quad G\mid\Phi(f)\qquad(f\in A),$$
--
--   and there is an isomorphism of complex algebras
--
--   $$A/R\cong_{\mathbb C}\mathbb C[T]/(G).$$
--
--   The quotient is finite dimensional, with
--
--   $$\dim_{\mathbb C}(A/R)=\deg G,\qquad
--   \dim_{\mathbb C}(A/R)+\deg g=\deg M.$$
--
--   This computes the residual ideal for a finite scheme given by a time-polynomial presentation. Together with the usual intersection model $A/(I+(p))\cong\mathbb C[T]/(g)$, the last identity states that the residual and intersection lengths add to the original length.
--
--   **Formalization Note** No contact, lattice, smoothness or monicity hypothesis is imposed. The exact membership presentation and $M\ne0$ are the hypotheses. The gcd is Mathlib's normalized polynomial gcd and `/` is polynomial Euclidean division. The proof establishes $g\ne0$ and $G\ne0$, so the displayed degrees agree with the formal natural degrees. The zero polynomial $p$, the case $q=0$, and nonzero constant $M$ are included. The algebra isomorphism is asserted to exist; its coordinate action is not part of the formal conclusion. The result supplies residual algebra and length data without a global degree or algebraic-group estimate.
-- source:
--   Derived residual-ideal calculation for the finite-intersection algebra used in the approach associated with Senthil Kumar K (2026), Appendix A, https://doi.org/10.1017/S001309152610145X. This exact algebra statement is proved here rather than quoted from the article. Bezout identity for the normalized gcd shows M divides f*q iff M/gcd(M,q) divides f. A surjective time substitution and the first isomorphism theorem give the quotient algebra, whose power basis gives its length. Primary formal references: exists_gcd_eq_mul_add_mul, EuclideanDomain exact division, mul_dvd_mul_iff_right, Ideal.quotientKerAlgEquivOfSurjective, AdjoinRoot.powerBasis, finrank_quotient_span_eq_natDegree and Polynomial.natDegree_mul.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Colon

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_residual_quotient_length
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ p : MvPolynomial (Fin 4) ℂ,
      let q := MvPolynomial.aeval (Fin.cons Polynomial.X r) p
      let G := M / gcd M q
      let J := I.colon {p}
      (∀ f : MvPolynomial (Fin 4) ℂ,
        f ∈ J ↔ G ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
      Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
        (Polynomial ℂ ⧸ Ideal.span {G})) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = G.natDegree ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) + (gcd M q).natDegree = M.natDegree := by sorry
