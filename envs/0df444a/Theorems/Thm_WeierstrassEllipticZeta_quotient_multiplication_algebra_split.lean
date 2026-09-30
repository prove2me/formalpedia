-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_quotient_multiplication_algebra_split
-- name    : WeierstrassEllipticZeta.quotient_multiplication_algebra_split
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T01:18:39.412457+00:00
-- url     : https://prove2.me/theorems/6e6c6968-062a-4a8f-9690-22e3da76df35
-- title:
--   Algebra splitting into nilpotent and invertible multiplication factors
-- statement:
--   Let $A$ be a commutative complex algebra and $I$ an ideal. Fix a basis $\beta$ of $A/I$ indexed by $\{0,\ldots,d-1\}$ and an algebra homomorphism $\rho:A\to\operatorname{Mat}_d(\mathbb C)$ whose value at $p$ is the matrix of multiplication by $[p]$ in this basis. Assume that for every $p\in A$,
--   $$\operatorname{im}\rho(p)^{2d}=\operatorname{im}\rho(p)^d.$$
--
--   For each $p$, define the power and residual ideals
--   $$J=I+(p^d),\qquad R=I:p^d=\{a\in A:ap^d\in I\}.$$
--   Then
--   $$J+R=A,\qquad J\cap R=JR=I,$$
--   and there is a complex-algebra isomorphism
--   $$A/I\simeq (A/J)\times(A/R).$$
--   The image of $p$ in $A/J$ has $d$th power zero, and its image in $A/R$ is a unit. Moreover, there exists $e\in A$ such that
--   $$e\in J,\qquad 1-e\in R,\qquad e^2-e\in I,$$
--   $$J=I+(e),\qquad R=I+(1-e).$$
--
--   This gives an algebraic decomposition into a factor with nilpotent multiplication by $p$ and a factor with invertible multiplication by $p$. The algebra $A$ may be infinite-dimensional. The case $d=0$, when $A/I$ is the zero algebra, is included.
-- source:
--   Derived finite-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. Stabilization of multiplication images from exponent d to 2d yields comaximality of I+(p^d) and I:p^d. The existing comaximal residual decomposition theorem gives the algebra product and complementary idempotents. The class of p is nilpotent in the first factor and a unit in the second, including the zero-dimensional case. Reuses the Proved theorem WeierstrassEllipticZeta.comaximal_residual_decomposition. Primary Mathlib references: Algebra.leftMulMatrix_mulVec_repr, Ideal.Quotient.mk_surjective, Submodule.mem_colon_singleton, Ideal.mem_span_singleton, isUnit_iff_exists_inv and isUnit_pow_iff. No new definitions.

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Commute.Units

open scoped Classical

theorem WeierstrassEllipticZeta.quotient_multiplication_algebra_split
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (I : Ideal A) (d : ℕ) (β : Module.Basis (Fin d) ℂ (A ⧸ I))
    (ρ : A →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : ∀ p : A, ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p))
    (hstable : ∀ p : A,
      LinearMap.range ((ρ p) ^ (2 * d)).mulVecLin =
        LinearMap.range ((ρ p) ^ d).mulVecLin) :
    ∀ p : A,
      let J := I ⊔ Ideal.span {p ^ d}
      let R := I.colon {p ^ d}
      J ⊔ R = ⊤ ∧ J ⊓ R = I ∧ J * R = I ∧
      Nonempty ((A ⧸ I) ≃ₐ[ℂ] (A ⧸ J) × (A ⧸ R)) ∧
      (Ideal.Quotient.mk J p) ^ d = 0 ∧ IsUnit (Ideal.Quotient.mk R p) ∧
      ∃ e : A,
        e ∈ J ∧ 1 - e ∈ R ∧ e * e - e ∈ I ∧
        J = I ⊔ Ideal.span {e} ∧ R = I ⊔ Ideal.span {1 - e} := by sorry
