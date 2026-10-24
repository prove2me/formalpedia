-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_hilbertSchmidt_complete_finiteRank_dense
-- name    : QAlgorithms.Papers.Independent.Next46.P02.hilbertSchmidt_complete_finiteRank_dense
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:32:41.170041+00:00
-- url     : https://prove2.me/theorems/64842d38-8d0e-41fa-af5f-2e36c8b4c4c8
-- title:
--   Hilbert–Schmidt completeness and finite-rank density
-- statement:
--   Let $H$ be a complete real or complex Hilbert space. The Hilbert–Schmidt class with the inner product $\langle T;S\rangle_2=\operatorname{tr}(S^*T)$ and norm $\|\cdot\|_2$ is complete, hence a Hilbert space. Every Hilbert–Schmidt $T$ admits finite-rank approximations in this norm: for every $\varepsilon>0$ there is a finite-rank endomorphism $S$ of $H$ with
--
--   $$
--   \|T-S\|_2<\varepsilon.
--   $$
--
--   Both $S$ and $T-S$ are Hilbert–Schmidt. These two conclusions concern the Hilbert–Schmidt topology, separately from trace-norm completeness and density.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 17, §5, unnumbered Hilbert–Schmidt completeness and finite-rank density

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF p.17, unnumbered (a),(b): Hilbert–Schmidt completeness, inner product
inducing the specified norm, and finite-rank density in that norm. -/
theorem hilbertSchmidt_complete_finiteRank_dense :
    InnerProductOn (IsHilbertSchmidt (F := F) (H := H)) hilbertSchmidtNorm hilbertSchmidtInner ∧
    CompleteIn (IsHilbertSchmidt (F := F) (H := H)) hilbertSchmidtNorm ∧
    FiniteRankDenseIn (IsHilbertSchmidt (F := F) (H := H)) hilbertSchmidtNorm := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
