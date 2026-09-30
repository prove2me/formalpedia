-- Prove2me | Theorems.Thm_Smooth4Algebra_support_cover_homology_budget
-- name    : Smooth4Algebra.support_cover_homology_budget
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T01:59:25.088764+00:00
-- url     : https://prove2.me/theorems/d08bf15b-650c-4c26-b2a6-6d4411e392b2
-- title:
--   Support-cover rank and homology obstruction for finite complexes
-- statement:
--   Let $K$ be any field, let $I$ be a finite coordinate index set of size $N$, and let $A,B$ be square matrices over $K$ indexed by $I$. Put $D=A+B$ and suppose $D^2=0$. Let $p\in\mathbb N$ satisfy $\operatorname{rank}A\le p$.
--
--   Choose total-cover row and column sets $R,C\subseteq I$, and separate row and column sets $R_B,C_B\subseteq I$ for $B$. Assume the actual entries satisfy
--
--   $$
--   i\notin R,\ j\notin C\Longrightarrow D_{ij}=0,
--   \qquad i\notin R_B,\ j\notin C_B\Longrightarrow B_{ij}=0.
--   $$
--
--   With $q=\min\{|R|+|C|,\ p+|R_B|+|C_B|\}$, the rank and actual vector-space homology obey
--
--   $$
--   \operatorname{rank}D\le q,
--   \qquad \dim_K(\ker D/\operatorname{im}D)\ge\max\{0,N-2q\}.
--   $$
--
--   This converts independently checked support covers into a homology obstruction, allowing arbitrary coefficients and all cancellations. Rows and columns are distinct cover vertices even when they share a coordinate label. Neither $A$ nor $B$ is required to square to zero separately; only their sum must. Empty coordinate sets are included.
--
--   The statement does not certify any saved table enumeration, barcode catalogue, knot-Floer interpretation, link realization, disk or exotic sphere. Its role is the general algebraic lemma needed before such application certificates can be checked.
-- source:
--   Ryan Shin, Table 22: a common-differential rank obstruction for Ui15/B1 and Ui15/G13, unpublished research note cycle12_table22_common_rank.md, Section 2, equations (5)–(7); SHA-256 04202f0649254279d91bad21875b82ddbd1a8fc8812454f5e3ca54b9c65b630e. The finite tables and geometric interpretation in subsequent sections are not part of this formalization.

import Mathlib
import Definitions.Def_Smooth4AlgebraHomology

set_option autoImplicit false

theorem Smooth4Algebra.support_cover_homology_budget {K ι : Type*} [Field K] [Fintype ι]
    (A B : Matrix ι ι K) (totalRows totalCols mixedRows mixedCols : Finset ι)
    (p : ℕ) (h_base_rank : A.rank ≤ p)
    (h_total : ∀ i j, i ∉ totalRows → j ∉ totalCols → (A + B) i j = 0)
    (h_mixed : ∀ i j, i ∉ mixedRows → j ∉ mixedCols → B i j = 0)
    (h_square : (A + B).mulVecLin.comp (A + B).mulVecLin = 0) :
    (A + B).rank ≤ min (totalRows.card + totalCols.card)
      (p + mixedRows.card + mixedCols.card) ∧
    Fintype.card ι - 2 * min (totalRows.card + totalCols.card)
      (p + mixedRows.card + mixedCols.card) ≤
        Module.finrank K (Smooth4Algebra.Homology (A + B).mulVecLin) := by sorry
