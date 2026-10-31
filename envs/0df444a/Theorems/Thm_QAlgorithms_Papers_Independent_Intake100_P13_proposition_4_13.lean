-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P13_proposition_4_13
-- name    : QAlgorithms.Papers.Independent.Intake100.P13.proposition_4_13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:11:12.304027+00:00
-- url     : https://prove2.me/theorems/b0667717-6309-473f-a40e-8659a80bddc6
-- title:
--   Proposition 4.13
-- statement:
--   Let $V$ be a Hausdorff real locally convex space and let $C\subseteq V'$ be a nonempty weak-star closed convex subset of its continuous real dual. Put $b_C(y)=\inf_{f\in C}f(y)$ and $s_C(y)=-b_C(y)$, with extended-real infima. Suppose $x\in B(C)=\{y:b_C(y)>-\infty\}$ and $s_C$ is bounded on a neighborhood of $x$ in $V$. Then all of the following hold:
--
--   1. For every $m\in\mathbb R$, the slice
--   $$
--   C_m=\{f\in C:f(x)\le m\}
--   $$
--   is equicontinuous on $V$ and weak-star compact. Equicontinuity means that some zero neighborhood $U$ satisfies $|f(y)|\le1$ for all $f\in C_m$ and $y\in U$.
--   2. The evaluation map $C\to\mathbb R$, $f\mapsto f(x)$, is proper: preimages of compact sets are compact in the weak-star subspace topology.
--   3. There exists an extreme point $f_0$ of $C$ such that $f_0(x)=\min_{f\in C}f(x)$.
--   4. The space $C$, with its weak-star subspace topology, is locally compact.
--
--   These conclusions supply compact dual slices and an attained supporting value. Slices below the minimum may be empty.
-- source:
--   A complex semigroup approach to group algebras of infinite dimensional Lie groups, arXiv:0709.1062v1, PDF p. 29, Proposition 4.13

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P13

namespace QAlgorithms.Papers.Independent.Intake100.P13

open Set Filter Topology

noncomputable section

universe u v w

section DualGeometry

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

variable [LocallyConvexSpace ℝ V] [T2Space V]

/-- Proposition 4.13, PDF p. 29: compact equicontinuous sublevel slices,
proper evaluation, attainment at an extreme point, and local compactness.
The support bound is on a neighborhood in V and uses extended reals;
thus finiteness is not obtained from a default real infimum. Properness
is expressed by compact preimages of compact sets. -/
theorem proposition_4_13
    (C : Set (WeakDual ℝ V)) (hC : C.Nonempty)
    (hClosed : IsClosed C) (hConvex : Convex ℝ C)
    (x : V) (hx : x ∈ boundedBelowDirections C)
    (hSupport : ∃ U ∈ 𝓝 x, ∃ M : ℝ, 0 ≤ M ∧
      ∀ y ∈ U, -(M : EReal) ≤ -evalInf C y ∧ -evalInf C y ≤ (M : EReal)) :
    (∀ m : ℝ, let slice := {f ∈ C | f x ≤ m};
      (∃ U ∈ 𝓝 (0 : V), ∀ f ∈ slice, ∀ y ∈ U, |f y| ≤ 1) ∧ IsCompact slice) ∧
    (∀ K : Set ℝ, IsCompact K → IsCompact {f : C | (f : WeakDual ℝ V) x ∈ K}) ∧
    (∃ f ∈ C.extremePoints ℝ, (f x : EReal) = evalInf C x) ∧
    LocallyCompactSpace C := by sorry

end DualGeometry

end

end QAlgorithms.Papers.Independent.Intake100.P13
