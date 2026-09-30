-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_multiplication_matrix
-- name    : WeierstrassEllipticZeta.triangular_multiplication_matrix
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T23:08:06.398964+00:00
-- url     : https://prove2.me/theorems/14d80484-a854-4aab-9298-9cea8ffa527d
-- title:
--   Multiplication matrices and the characteristic polynomial of the time coordinate
-- statement:
--   Let $A=\mathbb C[x_0,x_1,x_2,x_3]$ and let $I$ be an ideal of $A$. Let $M\in\mathbb C[t]$ be monic, set $d=\deg M$, and let $r_1,r_2,r_3\in\mathbb C[t]$. Write $\phi:A\to\mathbb C[t]$ for substitution of $(t,r_1,r_2,r_3)$ and $E:\mathbb C[t]\to A$ for substitution of $x_0$. Assume the exact membership criterion
--   $$p\in I\quad\Longleftrightarrow\quad M\mid\phi(p).$$
--
--   Let $q\in A$ and let $T:A\to\mathbb C[t]$ be complex-linear. Assume that, whenever $\deg b<d$ and $p-E(b)q\in I$, one has $b=T(p)$. Suppose $\beta$ is a basis of $A/I$, indexed by $0\leq j<d$, with
--   $$\beta_j=[x_0^j q],\qquad
--   \bigl(\operatorname{coord}_{\beta}[p]\bigr)_i=[t^i]T(p).$$
--
--   There exists a complex-algebra homomorphism $\rho:A\to\operatorname{Mat}_d(\mathbb C)$ such that $\rho(p)$ is the matrix of multiplication by $[p]$ in the basis $\beta$. Its entries are
--   $$\rho(p)_{ij}=[t^i]\bigl((\phi(p)t^j)\bmod M\bigr),$$
--   and its kernel is exactly $I$:
--   $$\rho(p)=0\quad\Longleftrightarrow\quad p\in I.$$
--   Writing $C=\rho(x_0)$, one has
--   $$\rho(p)=\phi(p)(C),\qquad \det(t\,1_d-C)=M(t).$$
--
--   Here $[p]$ denotes a residue class and $[t^i]$ denotes a coefficient. Polynomial evaluation at a matrix uses scalar matrices for coefficients. The remainder is division by the monic polynomial $M$. The case $d=0$, with zero-size matrices and characteristic polynomial $1$, is included. All presentation, uniqueness and basis hypotheses are explicit.
-- source:
--   Derived finite-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. Proved here under explicit monic presentation, division uniqueness and weighted basis-coordinate hypotheses, not quoted from the article. Multiplication matrices have entries given by coefficients of phi(p)*t^j modulo M, kernel I, and are polynomial evaluations in the time matrix. The time matrix has characteristic polynomial M by Cayley-Hamilton and the exact annihilator criterion. Primary Mathlib references: Algebra.leftMulMatrix, leftMulMatrix_injective, Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, charpoly_natDegree_eq_dim and Polynomial.eq_of_monic_of_dvd_of_natDegree_le. No Prove2Me theorem dependencies or new definitions.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_multiplication_matrix
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (hM : M.Monic) (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (q : MvPolynomial (Fin 4) ℂ)
    (T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ)
    (hunique : ∀ (p : MvPolynomial (Fin 4) ℂ) (b : Polynomial ℂ),
      b.degree < (M.natDegree : ℕ) →
      p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I → b = T p)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (hβ : ∀ j : Fin M.natDegree,
      β j = Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ j.val * q))
    (hcoord : ∀ (p : MvPolynomial (Fin 4) ℂ) (i : Fin M.natDegree),
      β.repr (Ideal.Quotient.mk I p) i = (T p).coeff i.val) :
    ∃ ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ,
      (∀ p : MvPolynomial (Fin 4) ℂ,
        ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p)) ∧
      (∀ (p : MvPolynomial (Fin 4) ℂ) (i j : Fin M.natDegree),
        ρ p i j = ((MvPolynomial.aeval (Fin.cons Polynomial.X r) p *
          Polynomial.X ^ j.val) %ₘ M).coeff i.val) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ, ρ p = 0 ↔ p ∈ I) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        ρ p = Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4)))
          (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)) ∧
      (ρ (MvPolynomial.X (0 : Fin 4))).charpoly = M := by sorry
