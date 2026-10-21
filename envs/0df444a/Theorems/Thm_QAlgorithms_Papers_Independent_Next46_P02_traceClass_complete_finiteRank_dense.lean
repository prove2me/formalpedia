-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_traceClass_complete_finiteRank_dense
-- name    : QAlgorithms.Papers.Independent.Next46.P02.traceClass_complete_finiteRank_dense
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:31:20.405326+00:00
-- url     : https://prove2.me/theorems/d169a24f-7ffc-4704-a5ad-6f0e8fec6b5d
-- title:
--   Trace-norm completeness and finite-rank density
-- statement:
--   Let $H$ be a complete real or complex Hilbert space. The modulus-defined trace class with its trace norm is a Banach space. Equivalently every trace-norm Cauchy sequence of trace-class operators has a trace-class limit in trace norm. Moreover, for every $T\in\mathcal B_1(H)$ and every $\varepsilon>0$ there is a finite-rank endomorphism $S$ such that
--
--   $$
--   \|T-S\|_1<\varepsilon.
--   $$
--
--   The approximation is on the full domain $H$; $S$ and $T-S$ are trace-class. Completeness and density are conclusions, not assumed properties of a supplied normed-space structure.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 15, §5, Theorem 5.5: trace-norm completeness and finite-rank density

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF pp.15–16, Theorem 5.5: trace-norm completeness AND finite-rank density,
with neither property supplied as a hypothesis or a class instance. -/
theorem traceClass_complete_finiteRank_dense :
    NormOn (F := F) (IsModulusTraceClass (F := F) (H := H)) modulusTraceNorm ∧
    CompleteIn (IsModulusTraceClass (F := F) (H := H)) modulusTraceNorm ∧
    FiniteRankDenseIn (IsModulusTraceClass (F := F) (H := H)) modulusTraceNorm := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
