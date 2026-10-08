-- Prove2me | Theorems.Thm_TensorNP_SymEigen_theorem_6_9
-- name    : TensorNP.SymEigen.theorem_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:46.401341+00:00
-- url     : https://prove2.me/theorems/e65d733c-dc3f-4871-90d5-d5e1c0a30e03
-- title:
--   Theorem 6.9 (Banach), (23) — for a symmetric 3-tensor, sup |S(x,y,z)|/(‖x‖‖y‖‖z‖) = sup |S(x,x,x)|/‖x‖³
-- statement:
--   Let $\mathcal S\in\mathbb R^{n\times n\times n}$ be a symmetric 3-tensor. Then both suprema below are finite and
--   $$\sup_{\mathbf x,\mathbf y,\mathbf z\neq\mathbf 0}\frac{|\mathcal S(\mathbf x,\mathbf y,\mathbf z)|}{\|\mathbf x\|_2\|\mathbf y\|_2\|\mathbf z\|_2}=\sup_{\mathbf x\neq\mathbf 0}\frac{|\mathcal S(\mathbf x,\mathbf x,\mathbf x)|}{\|\mathbf x\|_2^3}.$$
--   The left-hand side is the spectral norm $\|\mathcal S\|_{2,2,2}$ of Definition 6.6.
--
--   Banach's theorem says that the spectral norm of a symmetric tensor is attained on the diagonal $\mathbf x=\mathbf y=\mathbf z$. Hillar and Lim use it in §10 to identify the largest singular value, the spectral norm and the largest eigenvalue of a symmetric 3-tensor, which carries the hardness of Theorem 9.3 over to those problems.
--
--   **Formalization Note** The suprema are taken in $\mathbb R$ over nonzero vectors; finiteness (bounded above) is part of the conclusion, so the equality is not an artefact of the convention that an unbounded real supremum is $0$. For $n=0$ both sets are empty and both sides are $0$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:23, Theorem 6.9 (Banach), (23); spectral norm Definition 6.6, p. 0:22

import Mathlib
import Definitions.Def_TensorNP_SymEigen_Defs

namespace TensorNP.SymEigen

theorem theorem_6_9 {n : ℕ} (S : Tensor3 (Fin n)) (hS : IsSymmetric S) :
    BddAbove {r : ℝ | ∃ x y z : Fin n → ℝ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
        r = |trilinearForm S x y z| / (l2norm x * l2norm y * l2norm z)} ∧
      BddAbove {r : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ r = |cubicForm S x| / l2norm x ^ 3} ∧
      sSup {r : ℝ | ∃ x y z : Fin n → ℝ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
          r = |trilinearForm S x y z| / (l2norm x * l2norm y * l2norm z)} =
        sSup {r : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ r = |cubicForm S x| / l2norm x ^ 3} := by sorry

end TensorNP.SymEigen
