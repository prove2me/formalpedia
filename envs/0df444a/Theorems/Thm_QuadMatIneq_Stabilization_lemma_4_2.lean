-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_lemma_4_2
-- name    : QuadMatIneq.Stabilization.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:21.143031+00:00
-- url     : https://prove2.me/theorems/e1b6e746-fad0-43bc-8c8f-a3c3dc44a65d
-- title:
--   Lemma 4.2 (Strict S-lemma) — if N has a positive eigenvalue, xᵀMx > 0 on nonzero x with xᵀNx ⩾ 0 iff M − αN > 0 for some α ⩾ 0
-- statement:
--   Let $M,N\in\mathbb{S}^n$ and suppose that $N$ has at least one positive eigenvalue. Then
--   $$x^\top Mx>0\ \text{ for all nonzero } x\in\mathbb{R}^n \text{ with } x^\top Nx\geqslant 0 \quad\Longleftrightarrow\quad \exists\,\alpha\geqslant 0:\ M-\alpha N>0 .$$
--
--   The strict variant of the S-lemma; it is used in the proof of the strict matrix S-lemma (Theorem 4.10) when $N$ has a positive eigenvalue.
--
--   **Formalization Note** $M-\alpha N>0$ is `PosDef`; the eigenvalue hypothesis is as in Lemma 4.1.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Lemma 4.2, p. 9

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Lemma 4.2 (Strict S-lemma), p. 9. -/
theorem lemma_4_2 {k : Type*} [Fintype k] [DecidableEq k]
    (M N : Matrix k k ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hpos : ∃ i, 0 < hN.eigenvalues i) :
    (∀ x : k → ℝ, x ≠ 0 → 0 ≤ x ⬝ᵥ (N *ᵥ x) → 0 < x ⬝ᵥ (M *ᵥ x)) ↔
      ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosDef := by sorry

end QuadMatIneq.Stabilization
