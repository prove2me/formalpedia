-- Prove2me | Theorems.Thm_SolodovSvaiterVI_Alg21_linesearch_well_defined
-- name    : SolodovSvaiterVI.Alg21.linesearch_well_defined
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T10:29:49.953033+00:00
-- url     : https://prove2.me/theorems/08779af4-acaf-4499-af1c-5496e5c481d8
-- title:
--   The linesearch (2.1) of Algorithm 2.1 terminates
-- statement:
--   Let $C$ be a closed convex subset of $\mathbb{R}^n$, $F : \mathbb{R}^n \to \mathbb{R}^n$ continuous, and $\gamma, \sigma \in (0, 1)$. Let $r$ be the projected residual of $\mathrm{VI}(F, C)$. If $x \in C$ and $r(x) \ne 0$, then some nonnegative integer $k$ satisfies the linesearch condition
--
--   $$\langle F(x - \gamma^k r(x)), r(x) \rangle \ge \sigma \|r(x)\|^2. \tag{2.1}$$
--
--   Consequently the smallest such $k$, the index $k_i$ of Algorithm 2.1, exists, and every iteration of the method that has not stopped is well defined.
--
--   **Formalization Note** Stated for a generic point $x \in C$ with nonzero residual rather than for an iterate $x^i$.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 769, proof of Theorem 2.1, first paragraph (Eqs. (2.4)–(2.5))

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_ArmijoHolds

namespace SolodovSvaiterVI.Alg21

/-- Solodov–Svaiter, proof of Theorem 2.1, first paragraph (p. 769): the linesearch of
Algorithm 2.1 is well defined — at a point `x ∈ C` with `r(x) ≠ 0`, condition (2.1) holds for
some nonnegative integer `k`. -/
theorem linesearch_well_defined {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCc : IsClosed C) (hCcv : Convex ℝ C)
    (hF : Continuous F) (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1)
    (hσ0 : 0 < sigma) (hσ1 : sigma < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ C) (hr : residual F C x ≠ 0) :
    ∃ k : ℕ, ArmijoHolds F C gamma sigma x k := by sorry

end SolodovSvaiterVI.Alg21
