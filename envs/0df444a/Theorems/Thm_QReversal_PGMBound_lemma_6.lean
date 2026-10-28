-- Prove2me | Theorems.Thm_QReversal_PGMBound_lemma_6
-- name    : QReversal.PGMBound.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:58:41.712541+00:00
-- url     : https://prove2.me/theorems/619f8c07-fe42-4866-87d6-731cab860ba6
-- title:
--   Lemma 6: square-root block Frobenius mass is bounded by trace norm
-- statement:
--   Let $M$ be positive semidefinite with a two-by-two block decomposition
--   $$
--   M=\begin{pmatrix}a&b^\dagger\\b&c\end{pmatrix},
--   \qquad \sqrt M=\begin{pmatrix}x&y^\dagger\\y&z\end{pmatrix}.
--   $$
--   Then $|y|_2^2\leq|b|_1$, including rectangular off-diagonal blocks.
--
--   This is the block estimate that controls the recovery array's off-diagonal mass.
--
--   **Formalization Note** The lower-left blocks are selected from matrices indexed by the disjoint union of the two block index types.
-- source:
--   Barnum, Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, p. 13, Lemma 6, (43)–(44)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QReversal.PGMBound

theorem lemma_6 {m k : Type} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k]
    (M : Matrix (m ⊕ k) (m ⊕ k) ℂ) (hM : M.PosSemidef) :
    (∑ i : k, ∑ j : m, Complex.normSq
      ((CFC.sqrt M) (Sum.inr i) (Sum.inl j))) ≤
    WildeQIT.traceNorm (show Matrix k m ℂ from
      fun i j => M (Sum.inr i) (Sum.inl j)) := by sorry

end QReversal.PGMBound
