-- Prove2me | Theorems.Thm_ValuationSubring_exists_forall_eval_eq_zero_of_isUnit_det_jacobian
-- name    : ValuationSubring.exists_forall_eval_eq_zero_of_isUnit_det_jacobian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/3d0f946b-204c-57cb-aeeb-740be3a50e2b
-- title:
--   Multivariate Hensel lemma over a valuation subring of an algebraically closed field
-- statement:
--   Let $K$ be an algebraically closed field and $A \subseteq K$ a valuation subring, with $\mathfrak m$ its maximal ideal as a local ring. Let $\sigma$ be a finite index set, used simultaneously to index the unknowns and the equations. Given a family $F = (F_i)_{i \in \sigma}$ of polynomials $F_i \in A[(X_j)_{j \in \sigma}]$ and a point $P_0 \in A^{\sigma}$ such that, first, $F_i(P_0) \in \mathfrak m$ for every $i$, and second, the determinant of the Jacobian matrix $\bigl(\partial F_i/\partial X_j (P_0)\bigr)_{i,j \in \sigma}$, formed from the partial derivatives of the $F_i$ evaluated at $P_0$, is a unit of $A$, the conclusion asserts the existence of a point $P \in A^{\sigma}$ with $P_i - (P_0)_i \in \mathfrak m$ for every $i$ and $F_i(P) = 0$ for every $i$. Thus an approximate solution in $A$ with invertible Jacobian is refined to an exact solution congruent to it modulo $\mathfrak m$; only existence is asserted, no uniqueness.
--
--   This is the existence half of the multidimensional Hensel lemma, for a valuation ring whose fraction field is algebraically closed (for instance the valuation ring of $\overline{\mathbb Q}$ at a place); such rings are Henselian but in general neither Noetherian nor $\mathfrak m$-adically separated, so the complete-local form of the lemma is not directly available. It is used in the study of prolongations of points on modular curves along specialisations of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_forall_eval_eq_zero_of_isUnit_det_jacobian.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_forall_eval_eq_zero_of_isUnit_det_jacobian
    {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (F : σ → MvPolynomial σ A) (P₀ : σ → A)
    (hF : ∀ i, MvPolynomial.eval P₀ (F i) ∈ IsLocalRing.maximalIdeal A)
    (hJ : IsUnit (Matrix.det (Matrix.of fun i j : σ => MvPolynomial.eval P₀ (MvPolynomial.pderiv j (F i))))) :
    ∃ P : σ → A, (∀ i, P i - P₀ i ∈ IsLocalRing.maximalIdeal A) ∧ ∀ i, MvPolynomial.eval P (F i) = 0 := by sorry
