-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_lemma_4_1
-- name    : QuadMatIneq.Stabilization.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:32.05177+00:00
-- url     : https://prove2.me/theorems/05a48648-c30f-4a05-9649-d28b1fea74b0
-- title:
--   Lemma 4.1 (S-lemma) — if N has a positive eigenvalue, xᵀNx ⩾ 0 ⇒ xᵀMx ⩾ 0 iff M − αN ⩾ 0 for some α ⩾ 0
-- statement:
--   Let $M,N\in\mathbb{S}^n$ be symmetric matrices and suppose that $N$ has at least one positive eigenvalue. Then
--   $$x^\top Mx\geqslant 0\ \text{ for all } x\in\mathbb{R}^n \text{ with } x^\top Nx\geqslant 0 \quad\Longleftrightarrow\quad \exists\,\alpha\geqslant 0:\ M-\alpha N\geqslant 0 .$$
--
--   This is Yakubovich's S-lemma, recalled in the paper as the vector-valued base case from which the matrix S-lemma (Theorem 4.7) is derived. The positive-eigenvalue hypothesis is the Slater condition: some $\bar x$ has $\bar x^\top N\bar x>0$.
--
--   **Formalization Note** The index set is an arbitrary finite type; $M-\alpha N\geqslant 0$ is `PosSemidef`. The positive-eigenvalue hypothesis uses Mathlib's eigenvalues of the symmetric matrix $N$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Lemma 4.1, p. 9

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Lemma 4.1 (S-lemma), p. 9. -/
theorem lemma_4_1 {k : Type*} [Fintype k] [DecidableEq k]
    (M N : Matrix k k ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hpos : ∃ i, 0 < hN.eigenvalues i) :
    (∀ x : k → ℝ, 0 ≤ x ⬝ᵥ (N *ᵥ x) → 0 ≤ x ⬝ᵥ (M *ᵥ x)) ↔
      ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosSemidef := by sorry

end QuadMatIneq.Stabilization
