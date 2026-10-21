-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_nuclear_adjoint
-- name    : QAlgorithms.Papers.Independent.Next46.P02.nuclear_adjoint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:24:39.317581+00:00
-- url     : https://prove2.me/theorems/efd240e4-3f53-4321-a09b-441d0d9cc1cc
-- title:
--   Nuclearity and nuclear norm are invariant under adjoint
-- statement:
--   Let $H$ be a complete real or complex Hilbert space and let $T:H\to H$ be bounded linear, with Hilbert-space adjoint $T^*$. Nuclearity is defined by an absolutely norm-product-summable rank-one representation, and $\|\cdot\|_N$ is its infimal representation cost. Then
--
--   $$
--   T\text{ is nuclear}\iff T^*\text{ is nuclear},\qquad
--   \|T^*\|_N=\|T\|_N\quad\text{if }T\text{ is nuclear}.
--   $$
--
--   The absolute summability in the nuclear definition makes this result independent of the defective unguarded adjoint-series assertion in part (a).
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 8, §4, Corollary 4.3(b): nuclearity and nuclear norm under adjoint

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF pp.8–9, Corollary 4.3(b): adjoint preserves nuclearity and nuclear norm.
Part (a)'s unguarded adjoint-series assertion is separately deferred. -/
theorem nuclear_adjoint (T : H →L[F] H) :
    (IsNuclear T ↔ IsNuclear (ContinuousLinearMap.adjoint T)) ∧
      (IsNuclear T → banachNuclearNorm (ContinuousLinearMap.adjoint T) = banachNuclearNorm T) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
