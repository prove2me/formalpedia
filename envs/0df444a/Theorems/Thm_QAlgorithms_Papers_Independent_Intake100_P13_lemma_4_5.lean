-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P13_lemma_4_5
-- name    : QAlgorithms.Papers.Independent.Intake100.P13.lemma_4_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:09:52.047452+00:00
-- url     : https://prove2.me/theorems/ff0271d8-29b7-488a-b2ba-28812f2c3412
-- title:
--   Lemma 4.5
-- statement:
--   Let $V$ be a Hausdorff real locally convex space and $C\subseteq V'$ a weak-star closed convex subset of its continuous real dual. Define
--   $$
--   B(C)=\{x\in V:\inf_{f\in C}f(x)>-\infty\},\qquad
--   C^\circ=\{x\in V: |f(x)|\le1\text{ for every }f\in C\}.
--   $$
--   The following conditions are equivalent: $C$ is bounded for the weak-star topology; $B(C)=V$; and the absolute polar $C^\circ$ is absorbing in $V$. Here absorbing means that each vector belongs to $tC^\circ$ for all sufficiently large $|t|$. All three conditions hold for the empty set $C$.
--
--   This identifies pointwise boundedness of dual sets without replacing it by equicontinuity.
-- source:
--   A complex semigroup approach to group algebras of infinite dimensional Lie groups, arXiv:0709.1062v1, PDF p. 26, Lemma 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P13

namespace QAlgorithms.Papers.Independent.Intake100.P13

open Set Filter Topology

noncomputable section

universe u v w

section DualGeometry

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

variable [LocallyConvexSpace ℝ V] [T2Space V]

/-- Lemma 4.5, PDF p. 26: all three equivalent conditions, with the
weak-star topology, rather than a norm topology, on the continuous dual.
The empty C satisfies each condition. -/
theorem lemma_4_5
    (C : Set (WeakDual ℝ V)) (hClosed : IsClosed C) (hConvex : Convex ℝ C) :
    (Bornology.IsVonNBounded ℝ C ↔ boundedBelowDirections C = Set.univ) ∧
    (boundedBelowDirections C = Set.univ ↔ Absorbent ℝ (dualPolar C)) := by sorry

end DualGeometry

end

end QAlgorithms.Papers.Independent.Intake100.P13
