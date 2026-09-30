-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_ideal_residual_involution
-- name    : WeierstrassEllipticZeta.triangular_ideal_residual_involution
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T13:09:54.242088+00:00
-- url     : https://prove2.me/theorems/7da0227b-6fa6-4829-a3a5-a2dd5c970755
-- title:
--   Residual involution and complementary lengths for intermediate ideals
-- statement:
--   Let $A=\mathbb C[t,x_1,x_2,x_3]$ and choose $r_1,r_2,r_3\in\mathbb C[T]$. Define
--
--   $$\Phi:A\longrightarrow\mathbb C[T],\qquad \Phi(t)=T,\quad\Phi(x_i)=r_i(T).$$
--
--   Let $M\in\mathbb C[T]$ be nonzero, and let $I\subseteq A$ be an ideal satisfying
--
--   $$f\in I\quad\Longleftrightarrow\quad M\mid\Phi(f)\qquad(f\in A).$$
--
--   For every ideal $J\subseteq A$ containing $I$, set
--
--   $$R=I:J=\{f\in A:\ fJ\subseteq I\}.$$
--
--   Then $I\subseteq R$ and
--
--   $$I:R=J.$$
--
--   The quotient $A/R$ is finite dimensional over $\mathbb C$, and its length complements that of $A/J$:
--
--   $$\dim_{\mathbb C}(A/R)+\dim_{\mathbb C}(A/J)=\deg M.$$
--
--   For every other ideal $K$ containing $I$,
--
--   $$J\subseteq K\quad\Longleftrightarrow\quad I:K\subseteq R.$$
--
--   Thus taking the residual with respect to $I$ reverses inclusions and is an involution on the ideals containing $I$. In the algebra $A/I$, this is the double-annihilator property for all ideals, with complementary quotient lengths.
--
--   **Formalization Note** Each colon is by the entire ideal, regarded as a subset of $A$. The only hypotheses are the exact divisibility presentation, $M\ne0$, and the displayed ideal inclusions. The quotient $A/J$ is already finite dimensional by the intermediate-ideal presentation theorem; the new theorem explicitly asserts finite dimensionality of $A/R$. Natural degree is used formally, with $M\ne0$. The result includes $J=I$, $J=A$ and constant nonzero $M$. No contact, lattice or nonsingularity assumption is added, and no global zero estimate is asserted.
-- source:
--   Derived residual-ideal calculation for the finite-intersection algebra approach associated with Senthil Kumar K (2026), Appendix A, https://doi.org/10.1017/S001309152610145X. This exact algebraic statement is proved here, not quoted from the article. The Proved triangular_intermediate_ideal_presentation gives J=I+(g(t)) for a monic divisor g of M. The Proved triangular_residual_duality identifies I:J with I:g(t) and gives double residual equality. The Proved triangular_residual_quotient_length, Phi(g(t))=g and gcd(M,g)=g give complementary quotient lengths. General colon monotonicity and double residual equality give the inclusion equivalence. Primary formal references: Submodule.colon_mono, Ideal.le_colon, gcd_eq_right_iff and Polynomial.Monic.normalize_eq_self.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Colon

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_ideal_residual_involution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ J : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ J →
      let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
      I ≤ R ∧
      I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
      (∀ K : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ K →
        (J ≤ K ↔ I.colon (K : Set (MvPolynomial (Fin 4) ℂ)) ≤ R)) := by sorry
