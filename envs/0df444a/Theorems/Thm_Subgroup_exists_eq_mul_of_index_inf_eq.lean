-- Prove2me | Theorems.Thm_Subgroup_exists_eq_mul_of_index_inf_eq
-- name    : Subgroup.exists_eq_mul_of_index_inf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/354e1efc-f086-536e-b989-a19dc36fb967
-- title:
--   Index multiplicativity forces G = H₁H₂
-- statement:
--   Let $G$ be a finite group and let $H_1, H_2$ be subgroups of $G$. Assume the index identity $[G : H_1 \cap H_2] = [G : H_1]\cdot[G : H_2]$, written in Lean as `(H₁ ⊓ H₂).index = H₁.index * H₂.index` with `⊓` the intersection in the lattice of subgroups. Then for every $g \in G$ there exist $h_1 \in H_1$ and $h_2 \in H_2$ with $g = h_1 h_2$. Thus the conclusion is the element-wise form of $G = H_1 H_2$, with the factor from $H_1$ on the left, quantified over a single element $g$ fixed in the binders rather than packaged as a set-product equality.
--
--   This is the group-theoretic counterpart of the counting identity $|H_1H_2| = |H_1|\,|H_2|/|H_1 \cap H_2|$: in a finite group, multiplicativity of the index over an intersection is equivalent to the product decomposition $G = H_1H_2$. In this development it supplies the combinatorial input, via Galois theory, to the computation of $\sum_{\mathfrak{P}} e(\mathfrak{P})f(\mathfrak{P})$ over the places above a given place in [`AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber`](thm.html#AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_exists_eq_mul_of_index_inf_eq.lean

import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Subgroup.exists_eq_mul_of_index_inf_eq {G : Type*} [Group G] [Finite G] (H₁ H₂ : Subgroup G) (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) : ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ := by sorry
