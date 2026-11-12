-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_lemma_3
-- name    : PQNormIPM1352.Main.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:04.919931+00:00
-- url     : https://prove2.me/theorems/da5ab808-168e-4c97-8869-d9e85e0e6c9a
-- title:
--   Lemma 3 — variational characterization of the Schur complement
-- statement:
--   Let $A \in \mathbb R^{(n_1+n_2)\times(n_1+n_2)}$ be positive definite, with rows and columns partitioned into blocks $S_1, S_2$, and let
--   $$A\setminus S_2 = A(S_1,S_1) - A(S_1,S_2)\,A(S_2,S_2)^{-1}A(S_2,S_1) \tag{2}$$
--   be its Schur complement with respect to $S_2$. For any $x_1\in\mathbb R^{S_1}$,
--   $$x_1^\top(A\setminus S_2)\,x_1 = \min_{x_2\in\mathbb R^{S_2}}\begin{pmatrix}x_1\\x_2\end{pmatrix}^{\!\top} A\begin{pmatrix}x_1\\x_2\end{pmatrix},$$
--   and the minimum is attained at $x_2 = -A(S_2,S_2)^{-1}A(S_2,S_1)\,x_1$.
--
--   It is used to lift the error bound of the Schur-complement solve to the full Hessian norm in Lemma 11.
--
--   Differences from the source:
--   - encoding: A positive definite with A(S₂,S₂) invertible, blocks indexed by S₁, S₂ → A : Matrix (S₁ ⊕ S₂) (S₁ ⊕ S₂) ℝ positive definite, blocks by `toBlocks`; reason: A(S₂,S₂) is invertible because A is positive definite, so the source's invertibility assumption is implied
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Lemma 3, printed p. 5 (PDF p. 6); setting §2.1.4, p. 4

import Mathlib
open Matrix

namespace PQNormIPM1352.Main

/-- **Lemma 3** (Pirazzini–Spielman, STOC 2027 #1352, p. 5; setting of §2.1.4, p. 4). Let
`A ∈ ℝ^{(S₁ ⊔ S₂) × (S₁ ⊔ S₂)}` be positive definite, with blocks `A(Sᵢ, Sⱼ)` and Schur complement
`A \ S₂ = A(S₁,S₁) − A(S₁,S₂) A(S₂,S₂)⁻¹ A(S₂,S₁)` (2). For every `x₁ ∈ ℝ^{S₁}`,
`x₁ᵀ (A \ S₂) x₁ = min_{x₂ ∈ ℝ^{S₂}} (x₁; x₂)ᵀ A (x₁; x₂)`, and the minimum is attained at
`x₂ = −A(S₂,S₂)⁻¹ A(S₂,S₁) x₁`. -/
theorem lemma_3 {S₁ S₂ : Type} [Fintype S₁] [Fintype S₂] [DecidableEq S₁] [DecidableEq S₂]
    (A : Matrix (S₁ ⊕ S₂) (S₁ ⊕ S₂) ℝ) (hA : A.PosDef) (x₁ : S₁ → ℝ) :
    IsLeast {t : ℝ | ∃ x₂ : S₂ → ℝ, t = Sum.elim x₁ x₂ ⬝ᵥ (A *ᵥ Sum.elim x₁ x₂)}
        (x₁ ⬝ᵥ ((A.toBlocks₁₁ - A.toBlocks₁₂ * A.toBlocks₂₂⁻¹ * A.toBlocks₂₁) *ᵥ x₁)) ∧
      Sum.elim x₁ (-(A.toBlocks₂₂⁻¹ * A.toBlocks₂₁) *ᵥ x₁) ⬝ᵥ
          (A *ᵥ Sum.elim x₁ (-(A.toBlocks₂₂⁻¹ * A.toBlocks₂₁) *ᵥ x₁)) =
        x₁ ⬝ᵥ ((A.toBlocks₁₁ - A.toBlocks₁₂ * A.toBlocks₂₂⁻¹ * A.toBlocks₂₁) *ᵥ x₁) := by sorry

end PQNormIPM1352.Main
