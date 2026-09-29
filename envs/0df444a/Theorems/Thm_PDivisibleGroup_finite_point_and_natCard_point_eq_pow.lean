-- Prove2me | Theorems.Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow
-- name    : PDivisibleGroup.finite_point_and_natCard_point_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/aaa0788c-22ad-5222-8b0c-d649a9f4dad0
-- title:
--   Counting L-points of the levels of a p-divisible group in characteristic 0
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring, $h$ a natural number, and let $H$ be a $p$-divisible group of height $h$ over $O$ in the sense of the project's structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): a family of types $H.\mathrm{level}\,v$ ($v \in \mathbb{N}$), each a commutative ring carrying a cocommutative Hopf $O$-algebra structure and finite and free as an $O$-module, together with surjective coalgebra-and-algebra maps $H.\mathrm{level}\,(v+1) \to H.\mathrm{level}\,v$, the rank condition $\operatorname{rank}_O H.\mathrm{level}\,v = p^{vh}$, and the requirement that the kernel of the $v$-th transition map be the ideal `torsionIdeal` of $H.\mathrm{level}\,(v+1)$ at $p^v$, that is, the image of the augmentation ideal under multiplication by $p^v$. Let $L$ be an algebraically closed field of characteristic $0$ equipped with an $O$-algebra structure, and let $v$ be a natural number. Then the type $H.\mathrm{Point}\,L\,v$, namely the set of $O$-algebra homomorphisms $H.\mathrm{level}\,v \to L$ endowed with the convolution group structure, is finite, and its cardinality is exactly $p^{v h}$. The proof uses only the finiteness, freeness and rank of the individual level $H.\mathrm{level}\,v$, not the transition maps or the condition on their kernels.
--
--   This is the standard count of geometric points of the finite levels of a $p$-divisible group over a base in which the residue characteristic is invertible: in characteristic $0$ a finite commutative group scheme is étale, so the level $H_v$ has precisely $p^{vh}$ points over an algebraically closed field. It supplies the cardinality input to the later analysis of Tate modules and of torsion on Néron models of modular curves, and is cited in the study of the $p$-divisible group attached to $J_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.finite_point_and_natCard_point_eq_pow
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] {h : ℕ} (H : PDivisibleGroup O p h)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra O L] (v : ℕ) :
    Finite (H.Point L v) ∧ Nat.card (H.Point L v) = p ^ (v * h) := by sorry
