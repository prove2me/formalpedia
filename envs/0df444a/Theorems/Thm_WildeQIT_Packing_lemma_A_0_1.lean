-- Prove2me | Theorems.Thm_WildeQIT_Packing_lemma_A_0_1
-- name    : WildeQIT.Packing.lemma_A_0_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:07.135625+00:00
-- url     : https://prove2.me/theorems/584d7293-0d88-49aa-a3b6-e340c0a61bd8
-- title:
--   Lemma A.0.1: $M,N\ge0\Rightarrow M+N,\ MNM,\ NMN\ge0$
-- statement:
--   **Lemma A.0.1.** Let $M$ and $N$ be positive semi-definite operators on a finite-dimensional Hilbert space. Then the operators
--
--   $$M+N,\qquad MNM,\qquad NMN$$
--
--   are positive semi-definite.
--
--   It is used, for instance, to see that the coated codeword projectors $\Upsilon_x=\Pi\Pi_x\Pi$ of the square-root measurement are positive semi-definite.
--
--   **Formalization Note** Operators are complex square matrices indexed by a finite type.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Appendix A, Lemma A.0.1, p. 739

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Appendix A, Lemma A.0.1,
p. 739.
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.Packing

/-- **Lemma A.0.1** (Wilde, arXiv:1106.1445v8, p. 739). If `M` and `N` are positive
semi-definite operators, then `M + N`, `M N M` and `N M N` are positive semi-definite.

**Formalization Note.** Operators on a finite-dimensional Hilbert space are complex square
matrices indexed by a finite type `n`. -/
theorem lemma_A_0_1 {n : Type} [Fintype n] (M N : Matrix n n ℂ) (hM : M.PosSemidef) (hN : N.PosSemidef) : (M + N).PosSemidef ∧ (M * N * M).PosSemidef ∧ (N * M * N).PosSemidef := by sorry

end WildeQIT.Packing
