-- Prove2me | Theorems.Thm_WeierstrassCurve_j_mem_of_a_mem
-- name    : WeierstrassCurve.j_mem_of_a_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/63242fe7-1a80-5296-b967-717644bfb1a0
-- title:
--   The j-invariant lies in any subfield containing the aᵢ
-- statement:
--   Let $F$ be a field and let $S$ be a type of subobjects of $F$ that are subfields, i.e. a `SetLike` structure on $F$ satisfying `SubfieldClass`. Let $W$ be a Weierstrass curve over $F$, given by coefficients $a_1, a_2, a_3, a_4, a_6$ and assumed elliptic (its discriminant is a unit, so that the $j$-invariant $j = \Delta^{-1} c_4^3$ is defined). Let $K : S$ be such a subfield of $F$, and assume the five membership hypotheses $a_1 \in K$, $a_2 \in K$, $a_3 \in K$, $a_4 \in K$ and $a_6 \in K$. The conclusion is that $W.j \in K$. Because $S$ is an arbitrary `SubfieldClass`, the statement applies simultaneously to `Subfield F` and to intermediate fields of an extension. Note the shape: the curve itself remains a curve over $F$, and only its $j$-invariant is asserted to be a member of the subset $K$; nothing is claimed about a model of $W$ over $K$.
--
--   This is the elementary rationality statement that $j(E) \in \mathbb{Q}(a_1,a_2,a_3,a_4,a_6)$, in membership form rather than as a descent of the curve. It is used to show that the $j$-invariant of a Vélu quotient lies in a prescribed subfield, via [`WeierstrassCurve.veluQuotient_j_mem_of_mem`](thm.html#WeierstrassCurve.veluQuotient_j_mem_of_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_j_mem_of_a_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.j_mem_of_a_mem {F : Type*} [Field F] {S : Type*} [SetLike S F] [SubfieldClass S F]
    (W : WeierstrassCurve F) [W.IsElliptic] (K : S)
    (h₁ : W.a₁ ∈ K) (h₂ : W.a₂ ∈ K) (h₃ : W.a₃ ∈ K) (h₄ : W.a₄ ∈ K) (h₆ : W.a₆ ∈ K) : W.j ∈ K := by sorry
