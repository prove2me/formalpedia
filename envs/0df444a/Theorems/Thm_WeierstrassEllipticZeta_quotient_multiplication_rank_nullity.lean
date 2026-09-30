-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_quotient_multiplication_rank_nullity
-- name    : WeierstrassEllipticZeta.quotient_multiplication_rank_nullity
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T00:24:56.307237+00:00
-- url     : https://prove2.me/theorems/6729f7b0-2057-452e-a881-503806fe463c
-- title:
--   Ranks and nullities of quotient multiplication matrices from residual lengths
-- statement:
--   Let $A$ be a commutative complex algebra, let $I$ be an ideal, and fix a basis $\beta$ of the quotient $B=A/I$ indexed by $\{0,\ldots,d-1\}$. Let $\rho:A\longrightarrow\operatorname{Mat}_d(\mathbb C)$ be the algebra representation whose matrix $\rho(p)$ is multiplication by the class of $p$ in this basis.
--
--   For $p\in A$, put $R_p=I:p=\{a\in A:ap\in I\}$ and $J_p=I+(p)$. Assume the residual and intersection lengths satisfy
--   $$\dim_{\mathbb C}(A/R_p)+\dim_{\mathbb C}(A/J_p)=d\qquad(p\in A).$$
--   Then for every $p$, there is a complex-linear isomorphism
--   $$A/R_p\simeq\operatorname{im}\rho(p).$$
--   Consequently,
--   $$\operatorname{rank}\rho(p)=\dim_{\mathbb C}(A/R_p),\qquad
--   \dim_{\mathbb C}\ker\rho(p)=\dim_{\mathbb C}(A/J_p),$$
--   and
--   $$\operatorname{rank}\rho(p)+\dim_{\mathbb C}(A/J_p)=d.$$
--
--   The algebra $A$ itself need not be finite-dimensional. The case $d=0$ is included. In the contact-quotient application, the residual and intersection dimensions are already known from the triangular presentation and the contact multiplicities.
-- source:
--   Derived finite-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. Proved here for multiplication in a finite-dimensional quotient of a commutative complex algebra, assuming the stated residual-intersection length identity. This lemma is not quoted from the article. It identifies A/(I:p) with the matrix image, its dimension with matrix rank, and the intersection quotient dimension with nullity. Primary Mathlib references: Algebra.leftMulMatrix_mulVec_repr, LinearMap.quotKerEquivRange, Submodule.quotEquivOfEq, LinearMap.range_comp_of_range_eq_top, LinearEquiv.finrank_eq and LinearMap.finrank_range_add_finrank_ker. No Prove2Me theorem dependencies or new definitions.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped Classical

theorem WeierstrassEllipticZeta.quotient_multiplication_rank_nullity
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (I : Ideal A) (d : ℕ) (β : Module.Basis (Fin d) ℂ (A ⧸ I))
    (ρ : A →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : ∀ p : A, ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p))
    (hlength : ∀ p : A,
      Module.finrank ℂ (A ⧸ I.colon {p}) +
        Module.finrank ℂ (A ⧸ (I ⊔ Ideal.span {p})) = d) :
    ∀ p : A,
      Nonempty ((A ⧸ I.colon {p}) ≃ₗ[ℂ] LinearMap.range (ρ p).mulVecLin) ∧
      (ρ p).rank = Module.finrank ℂ (A ⧸ I.colon {p}) ∧
      Module.finrank ℂ (LinearMap.ker (ρ p).mulVecLin) =
        Module.finrank ℂ (A ⧸ (I ⊔ Ideal.span {p})) ∧
      (ρ p).rank + Module.finrank ℂ (A ⧸ (I ⊔ Ideal.span {p})) = d := by sorry
