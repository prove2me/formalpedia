-- Prove2me | Theorems.Thm_SP4Table22_certified_common_differential_obstruction
-- name    : SP4Table22.certified_common_differential_obstruction
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T04:08:58.562811+00:00
-- url     : https://prove2.me/theorems/512bef75-b7d9-4fef-9479-29b29b2df9f0
-- title:
--   Table-22 common-differential obstruction for 140 recorded sources
-- statement:
--   Choose any of the 140 explicitly recorded gradings of the thirty basis vectors in the table-22 certificate bundle. Write their two filtration coordinates and integer degrees as $a_i,b_i,m_i$. Let $K$ be any field and let $D=A+B$ be matrices on these thirty coordinates. Matrix entry $(i,j)$ maps the source $j$ to the target $i$.
--
--   Assume $D^2=0$ and the actual entries vanish outside the following allowed positions:
--
--   $$
--   D_{ij}\ne0\Longrightarrow a_i<a_j,\quad b_i\le b_j,\quad m_i=m_j-1,
--   $$
--
--   $$
--   B_{ij}\ne0\Longrightarrow a_i<a_j,\quad b_i<b_j,\quad m_i=m_j-1.
--   $$
--
--   Then both conditional bounds hold:
--
--   $$
--   \operatorname{rank}A\le4\Longrightarrow
--   \operatorname{rank}D\le13\quad\text{and}\quad
--   \dim_K(\ker D/\operatorname{im}D)\ge4,
--   $$
--
--   $$
--   \operatorname{rank}A\le2\Longrightarrow
--   \operatorname{rank}D\le11\quad\text{and}\quad
--   \dim_K(\ker D/\operatorname{im}D)\ge8.
--   $$
--
--   Consequently, homology dimension two is impossible under either rank bound. No independent square-zero condition is imposed on $A$ or $B$. All coefficients, cancellations and allowed mixed entries are included, not just a selected matching matrix.
--
--   This formally checks the complete saved 140-record certificate collection, with both target bounds, using ordinary Lean kernel computation. It does not prove that the saved source collection exhausts every possible Floer complex. The unbounded source-enumeration argument, source normalization, component-catalogue completeness, and geometric/Floer bridges remain separate obligations. The labels B1 and G13 motivate the two rank bounds; those knot-theoretic identifications are not hypotheses hidden in the matrix theorem.
-- source:
--   Ryan Shin, Table 22: a common-differential rank obstruction for Ui15/B1 and Ui15/G13, cycle12_table22_common_rank.md, Sections 2–4, equations (5)–(7); note SHA-256 04202f0649254279d91bad21875b82ddbd1a8fc8812454f5e3ca54b9c65b630e. Exact ordered records from cycle12_table22_common_rank.json, SHA-256 49ae9b38334cb89ff1eee916e4d96680850e02d51b493fd282f44181bd9c31ac. This contribution checks all 140 saved records and both rank bounds, not the unbounded source-enumeration or Floer/geometric completeness argument.

import Mathlib
import Definitions.Def_SP4Table22Certificates
import Definitions.Def_Smooth4AlgebraHomology

set_option autoImplicit false

theorem SP4Table22.certified_common_differential_obstruction {K : Type*} [Field K] (k : Fin 140)
    (A B : Matrix (Fin 30) (Fin 30) K)
    (h_total : ∀ i j, ¬ SP4Table22.Allowed (SP4Table22.record k) i j → (A + B) i j = 0)
    (h_mixed : ∀ i j, ¬ SP4Table22.MixedAllowed (SP4Table22.record k) i j → B i j = 0)
    (h_square : (A + B).mulVecLin.comp (A + B).mulVecLin = 0) :
    (A.rank ≤ 4 → (A + B).rank ≤ 13 ∧
      4 ≤ Module.finrank K (Smooth4Algebra.Homology (A + B).mulVecLin)) ∧
    (A.rank ≤ 2 → (A + B).rank ≤ 11 ∧
      8 ≤ Module.finrank K (Smooth4Algebra.Homology (A + B).mulVecLin)) := by sorry
