-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_coordinate_uniqueness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_coordinate_uniqueness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:13:48.146561+00:00
-- url     : https://prove2.me/theorems/49aa9c5f-a0f9-4f87-9cbe-9a617a212496
-- title:
--   Theorem 5.9
-- statement:
--   Let $S\subseteq k^d$ be arbitrary with its trace Borel sigma algebra, and let $\Phi,\Psi$ be measurable calculi on $S$ acting on the same $H$. Let $z_j$ be the restricted coordinates and $|z|^2=\sum_j|z_j|^2$. Each condition independently implies
--
--   $$\Phi=\Psi:\quad
--   \begin{cases}
--   \Phi(z_j)=\Psi(z_j)&\text{for every }j,\quad\text{or}\\
--   \Phi(z_j/(1+|z|^2))=\Psi(z_j/(1+|z|^2))&\text{for every }j,\ \Phi((1+|z|^2)^{-1})=\Psi((1+|z|^2)^{-1}),\quad\text{or}\\
--   \Phi(z_j/\sqrt{1+|z|^2})=\Psi(z_j/\sqrt{1+|z|^2})&\text{for every }j.
--   \end{cases}$$
--
--   The three conditions are alternatives; they are not simultaneous assumptions.
--
--   This determines the full calculus from coordinates or bounded regularizations.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 23, Theorem 5.9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Theorem 5.9, PDF pp.23–24: each of the three independent conditions suffices. -/
theorem calculus_coordinate_uniqueness {d : ℕ} (S : Set (Fin d → k))
    (F G : Symbol S k → Relation H) (hF : Calculus F) (hG : Calculus G) :
    ((∀ j, F (restrictedCoordinate S j) = G (restrictedCoordinate S j)) → F = G) ∧
    (((∀ j, F (times (restrictedCoordinate S j) (tupleRegularizer S)) = G (times (restrictedCoordinate S j) (tupleRegularizer S))) ∧
      F (tupleRegularizer S) = G (tupleRegularizer S)) → F = G) ∧
    ((∀ j, F (tupleRootCoordinate S j) = G (tupleRootCoordinate S j)) → F = G) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
