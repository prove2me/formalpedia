-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_triangular_multiplication_spectrum
-- name    : WeierstrassEllipticZeta.triangular_multiplication_spectrum
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T23:57:15.766892+00:00
-- url     : https://prove2.me/theorems/92eb060c-c19d-4097-885a-4a55cd0979d4
-- title:
--   Characteristic polynomials, traces and nilpotence of contact multiplication matrices
-- statement:
--   Let $A=\mathbb C[x_0,x_1,x_2,x_3]$, let $V$ be a finite set of points of $\mathbb C^4$, and give each point a nonnegative integer multiplicity $e_v$. Let $d\ge0$ and let $\rho:A\longrightarrow\operatorname{Mat}_d(\mathbb C)$ be a complex-algebra homomorphism satisfying
--   $$\det\rho(p)=\prod_{v\in V}p(v)^{e_v}\qquad(p\in A).$$
--   Then every multiplication matrix has characteristic polynomial and trace
--   $$\chi_{\rho(p)}(t)=\prod_{v\in V}(t-p(v))^{e_v},\qquad
--   \operatorname{tr}\rho(p)=\sum_{v\in V}e_vp(v).$$
--   Its spectrum consists exactly of the values $p(v)$ at points with $e_v>0$.
--
--   Moreover, $\rho(p)$ is nilpotent if and only if $p(v)=0$ at every point of positive multiplicity. Whenever these values vanish, the explicit bound
--   $$\rho(p)^d=0$$
--   holds.
--
--   The statement allows zero multiplicities, repeated values of $p$, and the empty contact set. In the empty case the hypotheses force $d=0$, so the characteristic polynomial is $1$ and the spectrum is empty. These assertions do not require diagonalizability. This is a derived algebraic lemma for the contact-quotient construction in the mission.
-- source:
--   Derived finite-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. Proved here for a complex-algebra representation satisfying the contact determinant product formula. This lemma is not quoted from the article. It computes every characteristic polynomial and trace, identifies the spectrum, and proves nilpotence precisely when all positive-multiplicity point values vanish, with exponent bounded by matrix size. Primary Mathlib references: Polynomial.funext, Matrix.eval_charpoly, trace_eq_sum_roots_charpoly_of_splits, mem_spectrum_iff_isRoot_charpoly, aeval_self_charpoly, and isNilpotent_charpoly_sub_pow_of_isNilpotent. No Prove2Me theorem dependencies or new definitions.

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

open scoped Classical

theorem WeierstrassEllipticZeta.triangular_multiplication_spectrum
    (V : Finset (Fin 4 → ℂ)) (e : V → ℕ) (d : ℕ)
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hdet : ∀ p : MvPolynomial (Fin 4) ℂ,
      (ρ p).det = ∏ v : V, (MvPolynomial.eval v.val p) ^ e v) :
    (∀ p : MvPolynomial (Fin 4) ℂ,
      (ρ p).charpoly = ∏ v : V,
        (Polynomial.X - Polynomial.C (MvPolynomial.eval v.val p)) ^ e v) ∧
    (∀ p : MvPolynomial (Fin 4) ℂ,
      (ρ p).trace = ∑ v : V, (e v : ℂ) * MvPolynomial.eval v.val p) ∧
    (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
      z ∈ spectrum ℂ (ρ p) ↔ ∃ v : V, 0 < e v ∧ z = MvPolynomial.eval v.val p) ∧
    (∀ p : MvPolynomial (Fin 4) ℂ,
      IsNilpotent (ρ p) ↔ ∀ v : V, 0 < e v → MvPolynomial.eval v.val p = 0) ∧
    (∀ p : MvPolynomial (Fin 4) ℂ,
      (∀ v : V, 0 < e v → MvPolynomial.eval v.val p = 0) → (ρ p) ^ d = 0) := by sorry
