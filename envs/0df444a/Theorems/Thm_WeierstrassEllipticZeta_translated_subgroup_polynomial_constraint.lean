-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_translated_subgroup_polynomial_constraint
-- name    : WeierstrassEllipticZeta.translated_subgroup_polynomial_constraint
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T05:21:37.206977+00:00
-- url     : https://prove2.me/theorems/9b17c941-1a51-458d-957a-f7b1f9017ea1
-- title:
--   Polynomial constraint from a translated analytic subgroup
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\wp',\zeta$. Let $\sigma$ be normalized entire sigma differential data. Let $S_0,\ldots,S_4$ be entire functions with no common zero, agreeing away from $\Lambda$ with
--
--   $$
--   (S_0,S_1,S_2,S_3,S_4)(z)
--   =\sigma(z)^3\bigl(1,\wp(z),\wp'(z),\zeta(z),
--   \wp'(z)\zeta(z)+2\wp(z)^2\bigr).
--   $$
--
--   Let $Q\in\mathbb C[Y_0,Y_1,X_0,\ldots,X_4]$ be homogeneous of degree $n\ge0$ in its last five variables. Suppose its entire pullback
--
--   $$
--   F_Q(z)=Q\bigl(1,z,S_0(z),\ldots,S_4(z)\bigr)
--   $$
--
--   is not identically zero. Let $V\subseteq\mathbb C^3$ be a complex linear subspace and let $r=(r_0,r_1,r_2)\in\mathbb C^3$ be arbitrary. Suppose, for every $v=(v_0,v_1,v_2)\in V$, that
--
--   $$
--   \begin{aligned}
--   0=Q\bigl(&1,r_0+v_0,S_0(r_1+v_1),S_1(r_1+v_1),S_2(r_1+v_1),\\
--   &S_3(r_1+v_1)+(r_2+v_2)S_0(r_1+v_1),\\
--   &S_4(r_1+v_1)+(r_2+v_2)S_2(r_1+v_1)\bigr).
--   \end{aligned}
--   $$
--
--   Then there exists a polynomial $P\in\mathbb C[T,X,Y,Z]$ such that
--
--   $$
--   \exists z\notin\Lambda:\quad
--   P\bigl(z,\wp(z),\wp'(z),\zeta(z)\bigr)\ne0
--   $$
--
--   and
--
--   $$
--   P\bigl(v_0,\wp(v_1),\wp'(v_1),v_2+\zeta(v_1)\bigr)=0
--   \quad(v\in V,\ v_1\notin\Lambda).
--   $$
--
--   This supplies the regular affine polynomial constraint required by the A.1 analytic subgroup criterion from containment of a translated subgroup in the original projective hypersurface. The translation coordinates need not be regular. The conclusion concerns the regular affine part; that part can be empty. The theorem does not construct $V$ or assert any multiplicity bound.
--
--   **Formalization Note.** This is the concrete analytic bridge for the translated-hypersurface condition in Appendix A, Theorem A.2 and the exponential description used in Lemma A.1 of [Senthil Kumar (2026)](https://doi.org/10.1017/S001309152610145X). The statement uses the mission's entire projective coordinates and does not assume a general algebraic subgroup classification.
-- source:
--   Senthil Kumar K (2026), Appendix A: Theorem A.2, equation (A.2), and §A.2 Lemma A.1 (exponential parametrization). https://doi.org/10.1017/S001309152610145X. Specialized analytic-coordinate formulation; translated polynomial-constraint bridge proved separately from the remaining multiplicity construction.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Quotient.Basic
open WeierstrassEllipticZeta MvPolynomial

theorem WeierstrassEllipticZeta.translated_subgroup_polynomial_constraint
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (V : Submodule ℂ (Fin 3 → ℂ)) (r : Fin 3 → ℂ)
    (hvanish : ∀ v ∈ V,
      eval ![1, r 0 + v 0, S 0 (r 1 + v 1), S 1 (r 1 + v 1),
        S 2 (r 1 + v 1), S 3 (r 1 + v 1) + (r 2 + v 2) * S 0 (r 1 + v 1),
        S 4 (r 1 + v 1) + (r 2 + v 2) * S 2 (r 1 + v 1)] Q = 0) :
    ∃ P : MvPolynomial (Fin 4) ℂ,
      (∃ z : ℂ, z ∉ L.lattice ∧
        eval ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z] P ≠ 0) ∧
      (∀ v ∈ V, v 1 ∉ L.lattice →
        eval ![v 0, L.weierstrassP (v 1), L.derivWeierstrassP (v 1),
          v 2 + weierstrassZeta L (v 1)] P = 0) := by sorry
