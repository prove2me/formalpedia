-- Prove2me | Theorems.Thm_VecBalPoly_lemma_4_2
-- name    : VecBalPoly.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:16:33.864696+00:00
-- url     : https://prove2.me/theorems/9b778aae-b36a-4680-a6c9-ee4c947a4ec9
-- title:
--   Lemma 4.2 — at most $4s/K+1/2$ eigenvalues at least $L/2$
-- statement:
--   At any state after cleanup with $s>K$ and $1<L\le2$, let $F\subseteq\mathbb R^V$ be the subspace spanned by the eigenvectors of $M$ with eigenvalues at least $L/2$. Then
--   $$\dim F\le\frac{4s}K+\frac12.$$
--
--   Proposition 4.5 eliminates the eigen-directions in $F$ by linear constraints; this lemma bounds how many constraints that takes.
--
--   Differences from the source:
--   - generalization: a state after cleanup of Algorithm 2.2 → any state satisfying IsClean (cube, V = {|x_j| < 1}, T_i ⊆ V, (2.2), (2.3) on medium rows, column norms ≤ 1); reason: every post-cleanup state of a run satisfies these conditions, and the proof uses only them
--   - encoding: M on ℝ^V and the span of its eigenvectors with eigenvalue ≥ L/2 → the V × V block MV (indexed by the subtype V) and the span of all v with MV v = μv for some μ ≥ L/2; reason: the same matrix and subspace; the zero vector adds nothing to the span
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - encoding: indices i ∈ [m], j ∈ [n] → Fin m, Fin n (0-based); reason: Lean convention; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma 4.2, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_VecBalPoly_IsClean
import Definitions.Def_VecBalPoly_L

namespace VecBalPoly

open Matrix

/-- **Lemma 4.2 (few large eigenvalues).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma 4.2, p.9 (PDF p.10): "At any state after cleanup with s > K and 1 < L ≤ 2, let F be
the subspace spanned by the eigenvectors of M with eigenvalues at least L/2. Then
dim F ≤ 4s/K + 1/2."

**Formalization Note** "State after cleanup" is `IsClean`. `M` on `ℝ^V` is its `V × V`
block `MV`, a matrix indexed by the subtype `V`; `F` is the span of the vectors `v` with
`MV v = μv` for some `μ ≥ L/2` (the zero vector adds nothing to the span). -/
theorem lemma_4_2 :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n), IsClean A st →
      K < (st.V.card : ℝ) → 1 < L A st → L A st ≤ 2 →
      (Module.finrank ℝ (Submodule.span ℝ
          {v : st.V → ℝ | ∃ μ : ℝ, L A st / 2 ≤ μ ∧ MV A st *ᵥ v = μ • v}) : ℝ)
        ≤ 4 * st.V.card / K + 1 / 2 := by sorry

end VecBalPoly
