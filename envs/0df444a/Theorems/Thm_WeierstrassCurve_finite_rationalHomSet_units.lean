-- Prove2me | Theorems.Thm_WeierstrassCurve_finite_rationalHomSet_units
-- name    : WeierstrassCurve.finite_rationalHomSet_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/97650530-fa5a-545b-844e-49617bf2c0aa
-- title:
--   Finiteness of the units of End of an elliptic curve
-- statement:
--   Let $F$ be a field, let $k$ be an algebraically closed field equipped with an $F$-algebra structure, and let $W$ be a Weierstrass curve over $F$ which is elliptic (invertible discriminant). Consider additive maps $u$ from the group of affine points of the base change $W_k$, in its `toAffine` presentation, to itself, and the set [`WeierstrassCurve.rationalHomSet k W W`](def/WeierstrassCurve_RationalEnd.html#L28) consisting of those $\alpha$ which are either the zero homomorphism or rationally represented: there exist four polynomials $nX, dX, nY, dY \in F[X][Y]$ and a finite subset $B \subseteq k$ such that for every pair $(x,y) \in k^2$ which is a nonsingular point of $W_k$ with $x \notin B$, the evaluations of $dX$ and $dY$ at $(x,y)$ (after base change of coefficients to $k$) are nonzero and $\alpha$ sends the affine point $(x,y)$ to the affine point with coordinates $nX(x,y)/dX(x,y)$ and $nY(x,y)/dY(x,y)$. The assertion is that the set of $u$ in [`WeierstrassCurve.rationalHomSet k W W`](def/WeierstrassCurve_RationalEnd.html#L28) for which there exists $v$ in the same set with $u \circ v = \mathrm{id}$ and $v \circ u = \mathrm{id}$ as additive endomorphisms is finite.
--
--   This is the finiteness of the unit group of the ring of $F$-rational endomorphisms of an elliptic curve, read on $k$-points, i.e. the classical finiteness of the automorphism group of an elliptic curve fixing the origin; note that a two-sided rational inverse is required, so bijective-but-not-invertible endomorphisms such as Frobenius are excluded. It is used downstream in the treatment of torsion and of automorphisms of elliptic curves, in particular by [`WeierstrassCurve.eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self`](thm.html#WeierstrassCurve.eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self) and in the computation of Hecke correspondences on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_finite_rationalHomSet_units.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.finite_rationalHomSet_units {F : Type*} [Field F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] : {u : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point | u ∈ WeierstrassCurve.rationalHomSet k W W ∧ ∃ v ∈ WeierstrassCurve.rationalHomSet k W W, u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _}.Finite := by sorry
