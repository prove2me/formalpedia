-- Prove2me | Theorems.Thm_PDivisibleGroup_natCard_torsionBy_points_eq_pow
-- name    : PDivisibleGroup.natCard_torsionBy_points_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/c157eeba-b953-5b1b-beed-6c81b4b949f5
-- title:
--   Order of the pⁿ-torsion of points of a p-divisible group
-- statement:
--   Let $R$ be a commutative ring and let $p,h$ be natural numbers (no primality is assumed). Let $G$ be a $p$-divisible group of height $h$ over $R$ in the sense of the project structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): a family of commutative rings $G.\mathrm{level}\,v$, each a cocommutative Hopf algebra over $R$ that is finite and free as an $R$-module, together with surjective coalgebra-and-algebra maps $G.\mathrm{transition}\,v : G.\mathrm{level}\,(v+1) \to G.\mathrm{level}\,v$ over $R$, such that $\operatorname{rank}_R G.\mathrm{level}\,v = p^{vh}$ and the kernel of $G.\mathrm{transition}\,v$ is the ideal `torsionIdeal` of $G.\mathrm{level}\,(v+1)$ at $p^v$, i.e. the image of the augmentation ideal under the $p^v$-fold sum map. Let $L$ be an algebraically closed field of characteristic zero which is an $R$-algebra, and let $n$ be a natural number. Write $G.\mathrm{Points}\,L$ for the additive group obtained as the direct limit over $v$ of the groups $G.\mathrm{Point}\,L\,v =$ `WithConv` $(G.\mathrm{level}\,v \to_{\mathrm{alg}[R]} L)$, written additively, along the transition-induced maps. Then the $\mathbb{Z}$-submodule of $G.\mathrm{Points}\,L$ annihilated by the integer $p^n$ has exactly $p^{nh}$ elements.
--
--   This is the standard point count for a $p$-divisible group over a base in which $p$ is invertible: over an algebraically closed field of characteristic zero the group scheme of $p^n$-torsion is étale of order $p^{nh}$, so its group of points has $p^{nh}$ elements. It is the input for the statement that the associated Tate module is free of rank $h$ over $\mathbb{Z}_p$, and it is used here in the analysis of $p$-divisible groups over rings of integers whose Tate module representation is inertially trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_natCard_torsionBy_points_eq_pow.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.natCard_torsionBy_points_eq_pow
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L] (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (G.Points L) ((p ^ n : ℕ) : ℤ)) = p ^ (n * h) := by sorry
