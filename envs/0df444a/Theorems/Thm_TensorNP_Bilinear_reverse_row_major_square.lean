-- Prove2me | Theorems.Thm_TensorNP_Bilinear_reverse_row_major_square
-- name    : TensorNP.Bilinear.reverse_row_major_square
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-01T20:43:44.039071+00:00
-- url     : https://prove2.me/theorems/82bce578-8284-4cc2-a957-51cd31c5e281
-- title:
--   Reversal of a row-major square matrix stream
-- statement:
--   Let $v$ be a nonnegative integer, let $X$ be a type, and let $m$ be a $v\times v$ matrix with entries in $X$. List its entries in row-major order, reading the columns of each row from left to right. Reversing this list gives the row-major list for the matrix $m'$ defined by
--
--   $$m'_{ij}=m_{v-1-i,\,v-1-j}. $$
--
--   The result includes the empty matrix. It is a reusable indexing fact for the graph-input encoder used in the tensor bilinear feasibility reduction: that encoder stores adjacency symbols in reverse order after scanning them.
--
--   **Formalization Note.** Row-major positions are represented by the standard equivalence between $\operatorname{Fin}(v)\times\operatorname{Fin}(v)$ and $\operatorname{Fin}(v^2)$, and finite-index reversal by `Fin.rev`.
-- source:
--   Derived indexing lemma for the graphCode row-major adjacency layout in TensorNP.Eigen.Defs, https://prove2.me/api/v1/definitions/0e6f3434-ae26-4ae0-adad-a0f75e3b99d4; used in the reduction for Hillar and Lim, Most Tensor Problems Are NP-Hard, Theorem 3.7, p. 0:17, https://arxiv.org/abs/0911.1393 . This indexing lemma is an implementation consequence, not a claim that the paper explicitly states it.

import Mathlib

theorem TensorNP.Bilinear.reverse_row_major_square {α : Type*} {v : ℕ} (m : Fin v → Fin v → α) :
    (List.ofFn (fun k : Fin (v*v) ↦
      m (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)).reverse =
    List.ofFn (fun k : Fin (v*v) ↦
      m (finProdFinEquiv.symm k).1.rev (finProdFinEquiv.symm k).2.rev) := by sorry
