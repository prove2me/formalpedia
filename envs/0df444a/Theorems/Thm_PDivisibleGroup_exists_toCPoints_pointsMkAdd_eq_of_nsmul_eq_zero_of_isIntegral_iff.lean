-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff
-- name    : PDivisibleGroup.exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/d565480c-362d-5d10-9a04-b38f5433e337
-- title:
--   p^k-torsion completed points come from level-k points
-- statement:
--   Let $p$ be a prime and let $R$ be a commutative ring equipped with an algebra structure on the algebraic closure $\mathrm{PadicAlgCl}\ p$ of $\mathbb{Q}_p$, subject to the hypothesis `hO` that an element $x$ of $\mathrm{PadicAlgCl}\ p$ is integral over $R$ precisely when $\|x\| \le 1$. Let $h$ be a natural number and let $G$ be a [`PDivisibleGroup R p h`](def/PDivisibleGroup_Basic.html#L199), that is, a family of commutative rings $G.\mathrm{level}\ v$ carrying cocommutative Hopf algebra structures over $R$, finite and free as $R$-modules with $\operatorname{finrank}_R G.\mathrm{level}\ v = p^{vh}$, together with surjective coalgebra–algebra transition maps $G.\mathrm{level}\,(v+1) \to G.\mathrm{level}\ v$ whose kernels are the torsion ideals $\mathrm{torsionIdeal}\ R\ (G.\mathrm{level}\,(v+1))\ (p^v)$, the images of the augmentation ideal under the $p^v$-fold multiplication map. Write $S$ for the integral closure of $R$ in $\mathrm{PadicAlgCl}\ p$. Let $k$ be a natural number and let $T$ be an element of $G.\mathrm{CPoints}\ S$, the group of families $(T_i)_{i}$ with $T_i \in G.\mathrm{Points}\ (S/(p^i))$ compatible under the reduction maps $S/(p^{i+1}) \to S/(p^i)$, and suppose $p^k \cdot T = 0$. Then there is an $R$-algebra homomorphism $t \colon G.\mathrm{level}\ k \to S$, viewed as an element of the convolution group $G.\mathrm{Point}\ S\ k$, whose image in $G.\mathrm{Points}\ S$ under `pointsMkAdd` has, as its family of reductions modulo the powers $p^i$, exactly $T$.
--
--   This is Tate's observation that the torsion subgroup of the group of completed points $G(S) = \varprojlim_i G(S/p^i)$ is the direct limit of the groups of points of the finite levels $G_v$, here for $S$ the valuation ring of $\mathbb{C}_p$ cut out by the hypothesis on integrality over $R$. It is used in the Cartier-duality step [`PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff`](thm.html#PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CompletedPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} (G : PDivisibleGroup R p h) (k : ℕ)
    (T : G.CPoints (integralClosure R (PadicAlgCl p))) (hT : (p ^ k) • T = 0) :
    ∃ t : G.Point (integralClosure R (PadicAlgCl p)) k,
      G.toCPoints (integralClosure R (PadicAlgCl p))
        (G.pointsMkAdd (integralClosure R (PadicAlgCl p)) k (Additive.ofMul t)) = T := by sorry
