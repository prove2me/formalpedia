-- Prove2me | Theorems.Thm_ShapleyNV_shapley_two_by_two
-- name    : ShapleyNV.shapley_two_by_two
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:06.396158+00:00
-- url     : https://prove2.me/theorems/f9919850-ed70-48bd-9341-4a44409163a5
-- title:
--   Shapley (1964), Thm 2.1, cited p.ec3 — every $2\times2$ submatrix has a saddle point ⟹ the matrix has one
-- statement:
--   Let $M = (M_{ik})$ be a real matrix with finitely many rows $i$ and columns $k$ (both index sets nonempty). Suppose every $2 \times 2$ submatrix has a saddle point: for all rows $i, i'$ and columns $k, k'$,
--
--   $$
--   \min\big( \max(M_{ik}, M_{i'k}),\ \max(M_{ik'}, M_{i'k'}) \big) = \max\big( \min(M_{ik}, M_{ik'}),\ \min(M_{i'k}, M_{i'k'}) \big).
--   $$
--
--   Then $M$ has a saddle point:
--
--   $$
--   \min_k \max_i M_{ik} = \max_i \min_k M_{ik}.
--   $$
--
--   The paper uses this theorem of Shapley to show that the matrix $(A_{jk}(x))$ of the Shapley extension has a saddle point (Lemma EC.2).
--
--   Differences from the source:
--   - generalization: applied to the K × K matrix A(x) → any real matrix indexed by nonempty finite types ι × κ; reason: this is Shapley's theorem as stated for arbitrary matrices; the K × K case is an instance
--   - encoding: 'has a saddle point' → min over columns of max over rows equals max over rows of min over columns (rows maximize); index repetitions allowed; reason: a pure saddle point exists exactly when these values agree; submatrices with a repeated index always have one
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), proof of Lemma EC.2, p.ec3 (PDF 24), citing L. S. Shapley, Some topics in two-person games (1964), Theorem 2.1

import Mathlib

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Shapley (1964), Theorem 2.1**, as cited in the proof of Lemma EC.2, p.ec3: if every 2×2
submatrix of a finite real matrix has a saddle point, the matrix has a saddle point.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), proof of Lemma EC.2, p.ec3 (PDF 24), citing L. S. Shapley, *Some topics in two-person
games*, 1964, Theorem 2.1.

**Formalization Note.** Rows `i` belong to the maximizing player and columns `k` to the minimizing
player. "The 2×2 submatrix on rows `i, i'` and columns `k, k'` has a saddle point" is
`min_col max_row = max_row min_col` on those four entries; "the matrix has a saddle point" is
`min_k max_i M i k = max_i min_k M i k`. Repeated indices are allowed (such submatrices always have
a saddle point). The index sets are arbitrary nonempty finite types. -/
theorem shapley_two_by_two {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (M : ι → κ → ℝ)
    (h2 : ∀ (i i' : ι) (k k' : κ),
      min (max (M i k) (M i' k)) (max (M i k') (M i' k')) =
        max (min (M i k) (M i k')) (min (M i' k) (M i' k'))) :
    Finset.univ.inf' Finset.univ_nonempty (fun k => Finset.univ.sup' Finset.univ_nonempty (fun i => M i k)) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => Finset.univ.inf' Finset.univ_nonempty (fun k => M i k)) := by sorry

end ShapleyNV
