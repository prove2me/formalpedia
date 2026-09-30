-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_quotient_multiplication_fitting
-- name    : WeierstrassEllipticZeta.quotient_multiplication_fitting
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T00:52:41.881444+00:00
-- url     : https://prove2.me/theorems/9b93b136-1ff4-4b15-be28-c076492fb5a1
-- title:
--   Fitting decomposition and stabilization of quotient multiplication powers
-- statement:
--   Let $A$ be a commutative complex algebra, let $I$ be an ideal, and let $\beta$ be a basis of $A/I$ indexed by $\{0,\ldots,d-1\}$. Suppose that $\rho:A\to\operatorname{Mat}_d(\mathbb C)$ is an algebra homomorphism and that $\rho(p)$ is the matrix of multiplication by the class of $p$ in the basis $\beta$.
--
--   For each $p\in A$, put $T=\rho(p)$. Its kernel and image at exponent $d$ are complementary subspaces of $\mathbb C^d$, and there is a complex-linear isomorphism
--   $$A/I\simeq\ker T^d\times\operatorname{im}T^d.$$
--   For every integer $N\ge d$,
--   $$\ker T^N=\ker T^d,\qquad \operatorname{im}T^N=\operatorname{im}T^d,$$
--   and the residual colon ideals satisfy
--   $$I:p^N=I:p^d.$$
--   Here $I:p^n=\{a\in A:ap^n\in I\}$. The ambient algebra $A$ need not be finite-dimensional, and the statement includes $d=0$.
-- source:
--   Derived finite-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. For a quotient of dimension d it proves that multiplication kernels, images and colon ideals stabilize at exponent d, and constructs the Fitting direct-sum decomposition. Primary Mathlib references: Module.End.ker_pow_eq_ker_pow_finrank_of_le, LinearMap.iterateRange, LinearMap.finrank_range_add_finrank_ker, LinearMap.eventually_isCompl_ker_pow_range_pow, Submodule.prodEquivOfIsCompl and Algebra.leftMulMatrix_mulVec_repr. No Prove2Me theorem dependencies or new definitions.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped Classical

theorem WeierstrassEllipticZeta.quotient_multiplication_fitting
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (I : Ideal A) (d : ℕ) (β : Module.Basis (Fin d) ℂ (A ⧸ I))
    (ρ : A →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : ∀ p : A, ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p)) :
    ∀ p : A,
      IsCompl (LinearMap.ker ((ρ p) ^ d).mulVecLin)
        (LinearMap.range ((ρ p) ^ d).mulVecLin) ∧
      Nonempty ((A ⧸ I) ≃ₗ[ℂ]
        (LinearMap.ker ((ρ p) ^ d).mulVecLin) ×
          (LinearMap.range ((ρ p) ^ d).mulVecLin)) ∧
      ∀ N : ℕ, d ≤ N →
        LinearMap.ker ((ρ p) ^ N).mulVecLin =
          LinearMap.ker ((ρ p) ^ d).mulVecLin ∧
        LinearMap.range ((ρ p) ^ N).mulVecLin =
          LinearMap.range ((ρ p) ^ d).mulVecLin ∧
        I.colon {p ^ N} = I.colon {p ^ d} := by sorry
