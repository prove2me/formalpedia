-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_remark_2_2_4
-- name    : ShapleySnowSG.Kernel.remark_2_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:39.579734+00:00
-- url     : https://prove2.me/theorems/b348b786-2a30-4e82-ba85-1c891677ed2f
-- title:
--   Remark 2.2.4, p. 8 — if B has nonzero entries of one sign, val(A − wB) = 0 has a unique solution w
-- statement:
--   Let $A$ and $B$ be real $I\times J$ matrices, with $I$ and $J$ finite and nonempty. If all the entries of $B$ are nonzero and of the same sign, then there is a unique $w\in\mathbb R$ such that
--   $$\mathrm{val}(A-wB)=0 .$$
--
--   Combined with Lemma 2.2.3 this shows that $\mathrm{val}(\Delta^k-w\Delta^0)=0$, and its reduced analogue, each have exactly one solution.
--
--   **Formalization Note** "Nonzero and of the same sign" is encoded as: all entries positive, or all entries negative.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 8, Remark 2.2.4

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Remark 2.2.4, p. 8: if all the entries of `B` are nonzero and of the same sign, there is a
unique `w ∈ ℝ` with `val(A − wB) = 0`. -/
theorem remark_2_2_4 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (A B : Matrix ι κ ℝ) (hB : (∀ i j, 0 < B i j) ∨ (∀ i j, B i j < 0)) :
    ∃! w : ℝ, IsMatVal (A - w • B) 0 := by sorry

end ShapleySnowSG.Kernel
