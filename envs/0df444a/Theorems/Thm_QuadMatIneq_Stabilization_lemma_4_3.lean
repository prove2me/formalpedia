-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_lemma_4_3
-- name    : QuadMatIneq.Stabilization.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:21.422951+00:00
-- url     : https://prove2.me/theorems/8da90e40-1bc9-4312-94db-a9ca375653e9
-- title:
--   Lemma 4.3 (Finsler's lemma) — xᵀMx > 0 on nonzero x with xᵀNx = 0 iff M − αN > 0 for some α ∈ ℝ
-- statement:
--   Let $M,N\in\mathbb{S}^n$. Then
--   $$x^\top Mx>0\ \text{ for all nonzero } x\in\mathbb{R}^n \text{ with } x^\top Nx=0 \quad\Longleftrightarrow\quad \exists\,\alpha\in\mathbb{R}:\ M-\alpha N>0 .$$
--
--   Finsler's lemma handles an equality constraint, with a multiplier of arbitrary sign and no Slater condition. The paper uses it for the case of the strict matrix S-lemma in which $N$ has no positive eigenvalue.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Lemma 4.3, p. 10

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Lemma 4.3 (Finsler's lemma), p. 10. -/
theorem lemma_4_3 {k : Type*} [Fintype k] [DecidableEq k]
    (M N : Matrix k k ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    (∀ x : k → ℝ, x ≠ 0 → x ⬝ᵥ (N *ᵥ x) = 0 → 0 < x ⬝ᵥ (M *ᵥ x)) ↔
      ∃ α : ℝ, (M - α • N).PosDef := by sorry

end QuadMatIneq.Stabilization
