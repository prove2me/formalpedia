-- Prove2me | Theorems.Thm_PDASNewton_MMatrix_mmatrix_block_signs
-- name    : PDASNewton.MMatrix.mmatrix_block_signs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:52.144621+00:00
-- url     : https://prove2.me/theorems/f8acbf47-64c9-422b-89f2-20ff55fbb9fd
-- title:
--   Appendix A, p. 20 — for an M-matrix A and every partition 𝓘, 𝓐: A_𝓘 regular, A_𝓘⁻¹ ≥ 0, A_𝓘⁻¹A_𝓘𝓐 ≤ 0
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an M-matrix: nonsingular, with $a_{ij} \le 0$ for $i \ne j$ and $A^{-1} \ge 0$ entrywise. Let $\mathcal{I} \subseteq \{1,\dots,n\}$ be any index set and $\mathcal{A}$ its complement. Then the principal block $A_{\mathcal{I}}$ is nonsingular and
--   $$A_{\mathcal{I}}^{-1} \ge 0, \qquad A_{\mathcal{I}}^{-1} A_{\mathcal{I}\mathcal{A}} \le 0,$$
--   both entrywise.
--
--   The paper takes these sign facts from Berman and Plemmons (p. 134); they are what makes every comparison argument of the proof of Theorem 3.2 work, and the invertibility guarantees that each step of the algorithm is well defined.
--
--   **Formalization Note** The nonsingularity of $A_{\mathcal{I}}$ is stated as a conclusion because Lean's matrix inverse is zero on singular matrices; without it the sign conclusions would be empty. For $\mathcal{I} = \emptyset$ the block is the empty matrix (determinant 1), and for $\mathcal{A} = \emptyset$ the product has no columns.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 20, Appendix A, proof of Theorem 3.2 (first sentence, citing [BP, p. 134])

import Mathlib
import Definitions.Def_PDASNewton_MMatrix_Setting

open Filter Topology Matrix

namespace PDASNewton.MMatrix

theorem mmatrix_block_signs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsMMatrix A)
    (S : Finset (Fin n)) :
    IsUnit (principal A S).det ∧ (∀ i j, 0 ≤ (principal A S)⁻¹ i j) ∧
      ∀ i j, ((principal A S)⁻¹ * offDiag A S) i j ≤ 0 := by sorry

end PDASNewton.MMatrix
