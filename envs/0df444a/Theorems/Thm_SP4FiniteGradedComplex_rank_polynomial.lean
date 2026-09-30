-- Prove2me | Theorems.Thm_SP4FiniteGradedComplex_rank_polynomial
-- name    : SP4FiniteGradedComplex.rank_polynomial
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T03:59:56.872047+00:00
-- url     : https://prove2.me/theorems/21de6763-174e-41a3-a387-a1088d76b9f3
-- title:
--   Rank-polynomial identity and saturation for actual finite graded complexes
-- statement:
--   Let $K$ be a field, $I$ a finite set, and $C_i$ a finite-dimensional $K$-vector space for each $i\in I$. Let $\sigma:I\to I$ be a permutation, let $g:I\to\mathbb Z$, and let
--
--   $$
--   d_i:C_i\longrightarrow C_{\sigma i}
--   $$
--
--   be linear maps satisfying $d_{\sigma i}d_i=0$. Suppose that a nonzero $d_i$ lowers the integer grade by one: $g(\sigma i)=g(i)-1$. Grades need not distinguish the summands. Define the actual homology at the target of the $i$-th block by
--
--   $$
--   H_{\sigma i}=\ker d_{\sigma i}/\operatorname{im}d_i,
--   \qquad r_i=\operatorname{rank}_K d_i.
--   $$
--
--   The image is regarded as a subspace of the kernel using the square-zero hypothesis. Let $D:\prod_i C_i\to\prod_i C_i$ be the total linear map characterized by $(Dx)_{\sigma i}=d_i(x_i)$, and form the finite integer Laurent polynomials
--
--   $$
--   P_C(q)=\sum_i\dim_K C_i\,q^{g(i)},\qquad
--   P_H(q)=\sum_i\dim_K H_{\sigma i}\,q^{g(\sigma i)},\qquad
--   Q(q)=\sum_i r_iq^{g(i)}.
--   $$
--
--   Then $D^2=0$, and
--
--   $$
--   \dim_K C_{\sigma i}=\dim_K H_{\sigma i}+r_i+r_{\sigma i},
--   \qquad
--   P_C(q)=P_H(q)+(1+q^{-1})Q(q),
--   \qquad
--   Q(1)=\operatorname{rank}_K D.
--   $$
--
--   Moreover, saturation $P_C(1)=P_H(1)$ forces $D=0$ and $d_i=0$ for every $i$.
--
--   This supplies the linear-algebraic rank-polynomial bridge needed before correction coefficients may be interpreted as ranks of actual differentials. The coefficients are ordinary integers in every field characteristic. The statement concerns finite permutation-indexed graded complexes; it asserts no Floer realization, common-coarsening theorem, geometric obstruction, or result about smooth four-spheres.
--
--   **Formalization Note.** The finite product is also the finite direct sum. The Laurent factor $1+q^{-1}$ is represented by addition to the grade shift by $-1$. Homology is a genuine quotient of a kernel by the image of the incoming differential, not an assumed dimension. Repeated grades are permitted; the proof sums their contributions. No theorem embedding every bounded integer-indexed complex into this presentation is included.
-- source:
--   Local research note outputs/cycle18_structural_primary_proof.md, Section 1, A rank-polynomial identity for arbitrary matrices: the displayed degreewise dimension identity, P_C=P_H+(1+q^-1)Q, Q(1)=rank(d), and saturation implication. Formalized for actual finite permutation-indexed graded complexes; no Floer or common-coarsening realization is included. Primary source SHA-256 68da60b83072393fd9491dae22acb095ffce76a18a1285658417457df46188e4.

import Definitions.Def_SP4FiniteGradedComplex

set_option autoImplicit false
open SP4FiniteGradedComplex SP4GradedLaurent

theorem SP4FiniteGradedComplex.rank_polynomial {K : Type*} [Field K] {I : Type*} [Fintype I]
    {C : I → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, FiniteDimensional K (C i)] (A : Data K I C) :
    (totalD A).comp (totalD A) = 0 ∧
    (∀ i, Module.finrank K (C (A.prev i)) = Module.finrank K (HomologyAtTarget A i) +
      blockRank A i + blockRank A (A.prev i)) ∧
    chainPolynomial A = homologyPolynomial A + tensorV (rankPolynomial A) ∧
    mass (rankPolynomial A) = (Module.finrank K (LinearMap.range (totalD A)) : ℤ) ∧
    (mass (chainPolynomial A) = mass (homologyPolynomial A) →
      totalD A = 0 ∧ ∀ i, A.d i = 0) := by sorry
