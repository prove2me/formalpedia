-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P13_proposition_4_4
-- name    : QAlgorithms.Papers.Independent.Intake100.P13.proposition_4_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:09:25.840279+00:00
-- url     : https://prove2.me/theorems/5c3f2768-eb89-49c4-b080-b45c63907a05
-- title:
--   Proposition 4.4
-- statement:
--   Let $V$ be a Hausdorff real locally convex space, and let $V'$ be its continuous real dual with the weak-star topology. Let $C\subseteq V'$ be weak-star closed and convex. For $x\in V$, put $b_C(x)=\inf\{f(x):f\in C\}$ in the extended real line, and set $B(C)=\{x:b_C(x)>-\infty\}$. If $B(C)$ has nonempty interior in $V$, then
--   $$
--   C=\{f\in V':\ f(x)\ge b_C(x)\text{ for every }x\in\operatorname{int}B(C)\}.
--   $$
--   The infimum of the empty set is $+\infty$, so the formula includes $C=\varnothing$.
--
--   The formula reconstructs a closed convex dual set using only evaluations in the interior of its lower-boundedness cone.
-- source:
--   A complex semigroup approach to group algebras of infinite dimensional Lie groups, arXiv:0709.1062v1, PDF p. 26, Proposition 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P13

namespace QAlgorithms.Papers.Independent.Intake100.P13

open Set Filter Topology

noncomputable section

universe u v w

section DualGeometry

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

variable [LocallyConvexSpace ℝ V] [T2Space V]

/-- Proposition 4.4, PDF p. 26: reconstruction from the interior of B(C).
No nonemptiness assumption on C is added. Extended infima preserve the
empty case, for which the reconstructed set is empty. -/
theorem proposition_4_4
    (C : Set (WeakDual ℝ V)) (hClosed : IsClosed C) (hConvex : Convex ℝ C)
    (hInterior : (interior (boundedBelowDirections C)).Nonempty) :
    C = {f | ∀ x ∈ interior (boundedBelowDirections C), evalInf C x ≤ (f x : EReal)} := by sorry

end DualGeometry

end

end QAlgorithms.Papers.Independent.Intake100.P13
