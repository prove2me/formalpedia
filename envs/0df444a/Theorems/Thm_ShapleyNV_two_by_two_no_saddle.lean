-- Prove2me | Theorems.Thm_ShapleyNV_two_by_two_no_saddle
-- name    : ShapleyNV.two_by_two_no_saddle
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:08.716605+00:00
-- url     : https://prove2.me/theorems/1ccc85fd-b704-4fca-882d-dc8ecb7012ef
-- title:
--   Proof of Lemma EC.2, p.ec3 — a $2\times2$ matrix without saddle point is diagonally dominant
-- statement:
--   Let $a, b, c, d$ be real numbers and consider the matrix $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$. If
--
--   $$
--   (a \wedge c) \vee (b \wedge d) \ne (a \vee b) \wedge (c \vee d),
--   $$
--
--   that is, the maximin differs from the minimax (the matrix has no saddle point), then the matrix has the diagonal dominant property: the two entries on one diagonal are strictly greater than the two entries on the other diagonal,
--
--   $$
--   \max(a, d) < \min(b, c) \quad\text{or}\quad \max(b, c) < \min(a, d).
--   $$
--
--   Here $\wedge$ and $\vee$ denote minimum and maximum.
--
--   Differences from the source: none.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), proof of Lemma EC.2, p.ec3 (PDF 24)

import Mathlib

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **A 2×2 matrix without a saddle point is diagonally dominant**, proof of Lemma EC.2, p.ec3.
For the matrix `(a b; c d)`, if `(a ∧ c) ∨ (b ∧ d) ≠ (a ∨ b) ∧ (c ∨ d)` then the two entries on one
diagonal are strictly greater than the two entries on the other diagonal.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), proof of Lemma EC.2, p.ec3 (PDF 24).

**Formalization Note.** `∧`/`∨` on reals are `min`/`max`. "One diagonal strictly greater than the
other" is `max a d < min b c ∨ max b c < min a d`. -/
theorem two_by_two_no_saddle (a b c d : ℝ)
    (h : max (min a c) (min b d) ≠ min (max a b) (max c d)) :
    max a d < min b c ∨ max b c < min a d := by sorry

end ShapleyNV
