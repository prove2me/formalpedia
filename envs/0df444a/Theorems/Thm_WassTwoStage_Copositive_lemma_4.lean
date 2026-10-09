-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_lemma_4
-- name    : WassTwoStage.Copositive.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:55:44.09153+00:00
-- url     : https://prove2.me/theorems/af2e6521-3c1b-49b2-a3e7-6cabe70e91f9
-- title:
--   Lemma 4 — copositive Schur complements
-- statement:
--   Consider the symmetric block matrix
--   $$M = \begin{bmatrix} A & B\\ B^\top & C\end{bmatrix}$$
--   with $A$ positive definite ($A \succ 0$) and $C$ symmetric. If the Schur complement is strictly copositive,
--   $$C - B^\top A^{-1}B \succ_{\mathcal C} 0,$$
--   then $M \succ_{\mathcal C} 0$, i.e. $v^\top M v > 0$ for every nonzero $v \ge 0$.
--
--   This is the copositive analogue of the Schur complement criterion for positive definiteness; it is used to build the Slater point in the proof of Theorem 4.
--
--   **Formalization Note** The blocks are indexed by arbitrary finite types. $A \succ 0$ is Mathlib's `PosDef` (symmetric, positive definite), which together with the symmetry of $C$ makes $M$ symmetric, as the paper requires.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 16, Lemma 4

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_Cones

open Matrix

namespace WassTwoStage.Copositive

/-- Lemma 4 (copositive Schur complements), Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 16: for the
symmetric matrix `M = [[A, B], [Bᵀ, C]]` with `A ≻ 0` (positive definite), `M ≻_C 0` holds if
`C − BᵀA⁻¹B ≻_C 0`. -/
theorem lemma_4 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hA : A.PosDef) (hC : C.IsSymm)
    (hS : StrictlyCopositive (C - Bᵀ * A⁻¹ * B)) :
    StrictlyCopositive (Matrix.fromBlocks A B Bᵀ C) := by sorry

end WassTwoStage.Copositive
