-- Prove2me | Theorems.Thm_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero
-- name    : PDivisibleGroup.cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/df64a48d-01ae-55ab-aa2f-81960b1efdb2
-- title:
--   p Gⁱ⊆ Gⁱ⁺¹ on completed points of G
-- statement:
--   Let $R$ be a commutative ring, let $p,h$ be natural numbers and let $G$ be a $p$-divisible group of height $h$ over $R$ in the Hopf-algebraic sense recorded by [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): a family of finite, free, cocommutative Hopf $R$-algebras `G.level v` with $\operatorname{rank}_R(\mathtt{level } v)=p^{vh}$, together with surjective coalgebra-algebra maps $\mathtt{level}(v+1)\to\mathtt{level } v$ whose kernels are the torsion ideals $\mathtt{torsionIdeal}(p^v)$, i.e. the images of the augmentation ideal under multiplication by $p^v$. Let $S$ be a commutative $R$-algebra and let $g$ be an element of `G.CPoints S`, that is, a family of points $g_i\in G(S/(p^i))$, each $G(\,\cdot\,)$ being the direct limit over $v$ of the point groups of `G.level v`, which is compatible with the maps induced by the reductions $S/(p^{i+1})\to S/(p^i)$. Let $i\ge 1$ and suppose the $i$-th component $\mathtt{cpointsProj } i\,(g)=g_i\in G(S/(p^i))$ vanishes. Then the $(i+1)$-st component of $p\cdot g$ vanishes, i.e. $\mathtt{cpointsProj }(i+1)\,(p\bullet g)=0$ in $G(S/(p^{i+1}))$.
--
--   This is the coordinate-free form of the standard congruence-filtration estimate for points of a $p$-divisible group: writing $G^j$ for the kernel of $G(S)^\wedge\to G(S/(p^j))$, it says $p\,G^i\subseteq G^{i+1}$ for $i\ge 1$, as in Step 4 of the proof of Tate's Proposition 11. It is used in the treatment of Cartier duality for completed points, where it feeds the vanishing criterion [`PDivisibleGroup.CartierDuality.cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff`](thm.html#PDivisibleGroup.CartierDuality.cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CompletedPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [CommRing S] [Algebra R S] (g : G.CPoints S) {i : ℕ} (hi : 1 ≤ i)
    (hg : G.cpointsProj S i g = 0) :
    G.cpointsProj S (i + 1) (p • g) = 0 := by sorry
