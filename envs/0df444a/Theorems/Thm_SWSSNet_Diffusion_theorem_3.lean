-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_theorem_3
-- name    : SWSSNet.Diffusion.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:08.399984+00:00
-- url     : https://prove2.me/theorems/0b98896d-9997-41b3-b54d-772233f8f7c8
-- title:
--   Theorem 3 — d(i,ℓ) = (eᵀB₁⁻¹)_ℓ/(eᵀB₁⁻¹)_i, and (eᵀB₁⁻¹)_i > 0
-- statement:
--   Let $B_1$ be the matrix of (38) for a pool $\hat\jmath$, and let $d$ be the class-to-class gains (13). Then
--   $$
--   d(i,\ell)=\frac{(e^{\mathsf T}B_1^{-1})_\ell}{(e^{\mathsf T}B_1^{-1})_i}\qquad\forall i,\ell, \qquad (45)
--   $$
--   and $(e^{\mathsf T}B_1^{-1})_i>0$ for every class $i$.
--
--   The theorem links the combinatorial gains of the tree to the linear part of the diffusion drift. It is the key step in expressing $\vartheta_p$ through $B_1$ (Theorem 4).
--
--   **Formalization Note** $(e^{\mathsf T}B_1^{-1})_\ell=\sum_k(B_1^{-1})_{k\ell}$. Lean's inverse of a singular matrix is $0$; the positivity clause therefore also asserts that $B_1$ is invertible. The statement is posed for the $B_1$ of every pool, each pool lying on an edge of the tree.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 19, Theorem 3, (45)

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Theorem 3, p. 19: for the matrix `B₁` of any pool `ĵ`,
`d(i,ℓ) = (eᵀB₁⁻¹)_ℓ / (eᵀB₁⁻¹)_i` (45) for all classes `i, ℓ`, and `(eᵀB₁⁻¹)_i > 0`. -/
theorem theorem_3 {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) :
    (∀ i ℓ : Fin I, gain N (Sum.inl i) (Sum.inl ℓ) =
      (∑ k, (B1 N ĵ)⁻¹ k ℓ) / (∑ k, (B1 N ĵ)⁻¹ k i)) ∧
    ∀ i : Fin I, 0 < ∑ k, (B1 N ĵ)⁻¹ k i := by sorry

end SWSSNet.Diffusion
