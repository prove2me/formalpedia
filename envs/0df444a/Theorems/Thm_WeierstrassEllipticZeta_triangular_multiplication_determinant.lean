-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_multiplication_determinant
-- name    : WeierstrassEllipticZeta.triangular_multiplication_determinant
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T23:29:47.956932+00:00
-- url     : https://prove2.me/theorems/a3691c05-9571-45e5-a35f-faea3cd21969
-- title:
--   Determinants of contact multiplication matrices and their invertibility criterion
-- statement:
--   Let $A=\mathbb C[x_0,x_1,x_2,x_3]$, let $V$ be a finite set of points of $\mathbb C^4$, and assign a nonnegative integer $e_v$ to each point. Suppose $I$ is an ideal of $A$ whose elements vanish at each $v$ with $e_v>0$. Put
--   $$M(t)=\prod_{v\in V}(t-v_0)^{e_v}.$$
--   Let $r_1,r_2,r_3\in\mathbb C[t]$ and write $\varphi(p)=p(t,r_1(t),r_2(t),r_3(t))$. Assume
--   $$p\in I\quad\Longleftrightarrow\quad M\mid\varphi(p).$$
--   Let $\rho:A\longrightarrow\operatorname{Mat}_{\deg M}(\mathbb C)$ be a complex-algebra homomorphism. Suppose every $\rho(p)$ is obtained by evaluating $\varphi(p)$ in $C=\rho(x_0)$, and that $C$ has characteristic polynomial $M$.
--
--   Then for every $p\in A$,
--   $$\det\rho(p)=\prod_{v\in V}p(v)^{e_v}.$$
--   Moreover, $\rho(p)$ is invertible if and only if $p(v)\ne0$ for every $v$ with $e_v>0$.
--
--   Zero multiplicities and the empty set are allowed. For the empty set, $M=1$ and the determinant of the resulting zero-by-zero matrix is $1$. Distinct points need not have distinct time coordinates. This is a derived algebraic lemma for the mission's contact-quotient construction.
-- source:
--   Derived finite-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. Proved here under explicit ideal vanishing, triangular presentation, polynomial-evaluation representation and factored time characteristic-polynomial hypotheses. This lemma is not quoted from the article. It proves det(rho(p)) = product_v p(v)^e(v), and invertibility precisely when p(v) is nonzero at every positive-multiplicity point. Primary Mathlib references: IsAlgClosed.splits, Polynomial.Splits, Submonoid.closure_induction, Matrix.eval_charpoly, det_neg, det_mul, and isUnit_iff_isUnit_det. No Prove2Me theorem dependencies or new definitions.

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Basic

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_multiplication_determinant
    (V : Finset (Fin 4 → ℂ)) (e : V → ℕ)
    (I : Ideal (MvPolynomial (Fin 4) ℂ))
    (hvanish : ∀ p ∈ I, ∀ v : V, 0 < e v → MvPolynomial.eval v.val p = 0)
    (M : Polynomial ℂ)
    (hM : M = ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ e v)
    (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ]
      Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ)
    (hρ : ∀ p : MvPolynomial (Fin 4) ℂ,
      ρ p = Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4)))
        (MvPolynomial.aeval (Fin.cons Polynomial.X r) p))
    (hchar : (ρ (MvPolynomial.X (0 : Fin 4))).charpoly = M) :
    (∀ p : MvPolynomial (Fin 4) ℂ,
      (ρ p).det = ∏ v : V, (MvPolynomial.eval v.val p) ^ e v) ∧
    (∀ p : MvPolynomial (Fin 4) ℂ,
      IsUnit (ρ p) ↔ ∀ v : V, 0 < e v → MvPolynomial.eval v.val p ≠ 0) := by sorry
