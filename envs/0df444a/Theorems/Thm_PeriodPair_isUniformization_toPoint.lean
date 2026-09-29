-- Prove2me | Theorems.Thm_PeriodPair_isUniformization_toPoint
-- name    : PeriodPair.isUniformization_toPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/cbff35ea-4fa5-52e2-9107-ed9c3b019fa2
-- title:
--   Uniformisation: z ↦ (wp(z), wp'(z)/2) parametrises E_Λ(ℂ)
-- statement:
--   Let $L$ be a period pair, with associated lattice `L.lattice` $\subset \mathbb{C}$, invariants `L.g₂`, `L.g₃` and Weierstrass curve `L.weierstrassCurve`, and let $h$ be a proof of `L.DiscriminantNeZero`, i.e. of $g_2^3 - 27 g_3^2 \neq 0$; this condition guarantees that the discriminant of `L.weierstrassCurve` is nonzero, so that every solution of the affine Weierstrass equation is a nonsingular point. Consider the map `L.toPoint h` from $\mathbb{C}$ to the group of points of the affine curve `L.weierstrassCurve.toAffine`, which sends $z \in$ `L.lattice` to the point at infinity $0$ and sends $z \notin$ `L.lattice` to the affine point with coordinates given by `L.weierstrassP` at $z$, these coordinates satisfying the curve equation by `L.equation_weierstrassP`. The theorem asserts `L.IsUniformization h`, that is, the conjunction of three statements: `L.toPoint h` is additive, $\Phi(z+w) = \Phi(z) + \Phi(w)$ for all $z, w \in \mathbb{C}$; it is surjective onto the group of points of the curve; and its kernel is contained in the lattice, $\Phi(z) = 0$ implying $z \in$ `L.lattice` (the converse inclusion holds by definition of $\Phi$). The proof cites [`PeriodPair.discriminant_ne_zero`](thm.html#PeriodPair.discriminant_ne_zero), which asserts that the hypothesis $g_2^3 - 27 g_3^2 \neq 0$ holds for every period pair.
--
--   This is the complex uniformisation theorem for elliptic curves in Weierstrass form: the Weierstrass parametrisation of a lattice induces a group isomorphism $\mathbb{C}/\Lambda \cong E_\Lambda(\mathbb{C})$. It underlies the subsequent transfer of analytic data to the algebraic curve, and is cited by the results comparing maps of period pairs with morphisms of the corresponding Weierstrass curves, such as [`PeriodPair.exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul`](thm.html#PeriodPair.exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul) and [`PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`](thm.html#PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_isUniformization_toPoint.lean

import Mathlib
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PeriodPair.isUniformization_toPoint (L : PeriodPair) (h : L.DiscriminantNeZero) :
    L.IsUniformization h := by sorry
