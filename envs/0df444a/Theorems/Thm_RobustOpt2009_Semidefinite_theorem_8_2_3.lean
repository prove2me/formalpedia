-- Prove2me | Theorems.Thm_RobustOpt2009_Semidefinite_theorem_8_2_3
-- name    : RobustOpt2009.Semidefinite.theorem_8_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:53.41099+00:00
-- url     : https://prove2.me/theorems/3332935b-b759-4aa3-bc40-8565815925cc
-- title:
--   Theorem 8.2.3 — Exact robust LMI with norm-bounded uncertainty
-- statement:
--   Let $d,n,p,q$ be natural numbers with $p>0$. Let $A^n:\mathbb R^d\to\mathbb S^n$ and $L:\mathbb R^d\to\mathbb R^{p\times n}$ be affine maps, let $R\in\mathbb R^{q\times n}$ be a fixed nonzero matrix, and let $\rho>0$. For every design vector $y\in\mathbb R^d$, the robust constraint
--   $$A^n(y)+L(y)^T\zeta R+R^T\zeta^T L(y)\succeq0\qquad\text{for every }\zeta\in\mathbb R^{p\times q}\text{ with }\|\zeta\|_{2,2}\le\rho$$
--   holds if and only if there is a real scalar $\lambda$ such that
--   $$\begin{bmatrix}\lambda I_p&\rho L(y)\\\rho L(y)^T&A^n(y)-\lambda R^TR\end{bmatrix}\succeq0.$$
--
--   Thus the robust feasible designs are exactly the projection onto $y$ of the feasible set of this single block linear matrix inequality in $(y,\lambda)$.
--
--   **Formalization Note** Matrices are real matrices indexed by `Fin`; affine dependence is expressed by Mathlib affine maps. The scoped matrix norm is the induced Euclidean operator norm, and positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, including symmetry. The statement uses the source's fixed-$R$ orientation and keeps $R\ne0$. The conventional positive row dimension is explicit; $R\ne0$ forces $n,q>0$. The design dimension may be zero, which represents constant data. No invertibility or strict positivity of $A^n(y)$ is assumed. The multiplier is unrestricted in the binder, as in (8.2.7); its nonnegativity follows from the upper-left block.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Theorem 8.2.3, printed pp. 206–207 (PDF pp. 232–233); standing assumptions pp. 204–205 (PDF pp. 230–231).

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustOpt2009.Semidefinite

/-- Theorem 8.2.3, with the affine data and positive uncertainty level of
§8.2.1: robust feasibility is exactly the projection of (8.2.7). -/
theorem theorem_8_2_3 {d n p q : ℕ} (hp : 0 < p)
    (A : (Fin d → ℝ) →ᵃ[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (L : (Fin d → ℝ) →ᵃ[ℝ] Matrix (Fin p) (Fin n) ℝ)
    (hA : ∀ y, (A y).IsSymm)
    (R : Matrix (Fin q) (Fin n) ℝ) (hR : R ≠ 0)
    (ρ : ℝ) (hρ : 0 < ρ) (y : Fin d → ℝ) :
    (∀ ζ : Matrix (Fin p) (Fin q) ℝ, ‖ζ‖ ≤ ρ →
      (A y + (L y)ᵀ * ζ * R + Rᵀ * ζᵀ * L y).PosSemidef) ↔
    ∃ lam : ℝ,
      (fromBlocks (lam • (1 : Matrix (Fin p) (Fin p) ℝ))
        (ρ • L y) (ρ • (L y)ᵀ) (A y - lam • (Rᵀ * R))).PosSemidef := by sorry

end RobustOpt2009.Semidefinite
