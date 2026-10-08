-- Prove2me | Theorems.Thm_WhitneyMatroid_Fano_exists_matroidOf_matrix
-- name    : WhitneyMatroid.Fano.exists_matroidOf_matrix
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:49:27.586153+00:00
-- url     : https://prove2.me/theorems/d47f6eb1-2d3f-4170-a911-7545aeaef27a
-- title:
--   §12 — the columns of a real matrix form a matroid
-- statement:
--   Let $\mathbf M$ be a real $m\times n$ matrix with columns $C_1,\dots,C_n$, and for a set $N$ of columns let $r(N)$ be the rank of the submatrix formed by $N$. Then there is a matroid $M$ whose elements are the columns and whose rank function is $r$:
--
--   $$
--   \exists\, M:\qquad r_M(N)=\operatorname{rank}\bigl(\mathbf M[\,\cdot\,,N]\bigr)\quad\text{for every set } N \text{ of columns}.
--   $$
--
--   This is the basic link between matrices and matroids in Whitney's paper: it makes "the matroid of a matrix" well defined, and every statement of the mission about matrices is about this matroid.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 525, §12

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf

namespace WhitneyMatroid.Fano

/-- Whitney §12 (p. 525): the columns of a real `m × n` matrix, with the rank of a set of columns
taken to be the rank of the submatrix they form, are the elements of a matroid. -/
theorem exists_matroidOf_matrix {ι : Type*} [Fintype ι] (m : ℕ) (A : Matrix (Fin m) ι ℝ) :
    ∃ M : Matroid ι, IsMatroidOf M A := by sorry

end WhitneyMatroid.Fano
