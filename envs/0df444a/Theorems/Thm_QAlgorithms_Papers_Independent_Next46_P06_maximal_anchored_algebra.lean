-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_maximal_anchored_algebra
-- name    : QAlgorithms.Papers.Independent.Next46.P06.maximal_anchored_algebra
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:40:59.136409+00:00
-- url     : https://prove2.me/theorems/f986c6c2-4bcd-4bb8-82f2-0d2a8ea1cdd5
-- title:
--   Theorem 6.4
-- statement:
--   Let $F$ be a unital complex algebra, $E\subseteq F$ a possibly nonunital complex subalgebra, and $\rho:E\to\mathcal L(X)$ a nondegenerate representation on a complex Banach space. Nondegenerate means that $E$ is a nonempty common-kernel anchor. Then
--
--   $$F_\rho:=\{f\in F:\forall e\in E,\ [ef]_E\text{ is a }\rho\text{-anchor}\}$$
--
--   is a unital complex subalgebra containing $E$ and anchored in $E$. Every unital subalgebra of $F$ containing $E$ and anchored in $E$ is contained in $F_\rho$. The carrier is constructed from $E,\rho$, rather than freely quantified.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 15, Theorem 6.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Theorem 6.4, PDF pp.15–16: the concrete carrier (6.2) is unital,
contains E, is anchored, and contains every unital subalgebra with those properties. -/
theorem maximal_anchored_algebra [CompleteSpace X] (rho : F → X →L[ℂ] X) (E : Set F)
    (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) :
    UnitalSubalgebraSet (maximalAnchored rho E) ∧ E ⊆ maximalAnchored rho E ∧
    AnchoredSet (representationGraphs rho) E (maximalAnchored rho E) ∧
    ∀ S : Subalgebra ℂ F, E ⊆ (S : Set F) →
      AnchoredSet (representationGraphs rho) E (S : Set F) → (S : Set F) ⊆ maximalAnchored rho E := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
