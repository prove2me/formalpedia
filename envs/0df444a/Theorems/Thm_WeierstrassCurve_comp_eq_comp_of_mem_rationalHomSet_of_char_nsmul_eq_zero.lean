-- Prove2me | Theorems.Thm_WeierstrassCurve_comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero
-- name    : WeierstrassCurve.comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/094b1237-94e1-5b16-b9aa-78bd4c0515b1
-- title:
--   Commutativity of rational endomorphisms of an ordinary curve
-- statement:
--   Let $k$ be an algebraically closed field of characteristic a prime $p$, and let $W$ be a Weierstrass curve over $k$ which is elliptic (`W.IsElliptic`). Suppose there is a point $T$ of the group $W(k)$ of points of the associated affine curve with $T \neq 0$ and $p \cdot T = 0$; that is, $W$ is ordinary in the sense of having a nonzero $k$-rational point killed by $p$. Let $\alpha$ and $\beta$ be additive endomorphisms of $W(k)$, each belonging to [`WeierstrassCurve.rationalHomSet k W W`](def/WeierstrassCurve_RationalEnd.html#L28), i.e. each is either the zero homomorphism or is rationally represented: there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $k$ and a finite subset $B \subseteq k$ such that for every nonsingular point $(x,y)$ of the curve with $x \notin B$ the denominators $d_X, d_Y$ do not vanish at $(x,y)$ and the homomorphism sends $(x,y)$ to the affine point with coordinates $n_X(x,y)/d_X(x,y)$ and $n_Y(x,y)/d_Y(x,y)$ (evaluation being taken through the base change of $W$ along the identity of $k$). The conclusion is that $\alpha$ and $\beta$ commute: $\alpha \circ \beta = \beta \circ \alpha$ as additive endomorphisms of $W(k)$.
--
--   This is Deuring's theorem that the ring of (rational) endomorphisms of an ordinary elliptic curve in characteristic $p$ is commutative, here in the form that any two rationally represented endomorphisms of such a curve commute. It is used in [`WeierstrassCurve.comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp`](thm.html#WeierstrassCurve.comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp), where commutation with iterates of Frobenius is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.comp_eq_comp_of_mem_rationalHomSet_of_char_nsmul_eq_zero {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) [W.IsElliptic] {T : W.toAffine.Point} (hT : T ≠ 0) (hpT : p • T = 0) {α β : W.toAffine.Point →+ W.toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W W) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W) : α.comp β = β.comp α := by sorry
