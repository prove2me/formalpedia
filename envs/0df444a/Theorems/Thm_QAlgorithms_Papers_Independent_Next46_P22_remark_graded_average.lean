-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_remark_graded_average
-- name    : QAlgorithms.Papers.Independent.Next46.P22.remark_graded_average
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:43:53.801655+00:00
-- url     : https://prove2.me/theorems/8c25fcc2-2daa-4655-b7b4-617b43bb6a96
-- title:
--   Remark after Lemma 4 (graded averaging)
-- statement:
--   Let $G$ be any group, $F$ any field, and $V=\bigoplus_gV^{(g)}$, $W=\bigoplus_gW^{(g)}$ internally graded vector spaces. For any linear $r:V\to W$, let $p_{V,g}$ and $p_{W,g}$ be the homogeneous projections. Hopf averaging with the canonical $FG$-coactions and coefficient-at-identity integral is exactly
--
--   $$\widetilde r(x)=\sum_{g\in G}p_{W,g}\bigl(r(p_{V,g}x)\bigr).$$
--
--   This sum is finite for every $x$, because its homogeneous decomposition has finite support. The resulting map is $F$-linear and preserves degree. No analytic summability convention is involved.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 8, Remark after Lemma 4 (graded averaging)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Remark after Lemma 4, PDF p.8: sum p_W,g r p_V,g, finite on each input. -/
theorem remark_graded_average {G : Type*} [Group G]
    (D : Grading F G V) (E : Grading F G W) (r : V →ₗ[F] W) :
    (∀ x, averageFromCoactions (gradedCoaction D) (gradedCoaction E)
      (identityCoefficient (F := F) (G := G)) r x = gradedAverage D E r x) ∧
    LinearFunction (F := F) (gradedAverage D E r) ∧ GradedMap D E (gradedAverage D E r) := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
