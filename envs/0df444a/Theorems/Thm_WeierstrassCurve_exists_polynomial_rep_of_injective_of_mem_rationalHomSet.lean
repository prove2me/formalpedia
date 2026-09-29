-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet
-- name    : WeierstrassCurve.exists_polynomial_rep_of_injective_of_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/92dd5725-7258-5583-ad6b-6d9cb146cfb0
-- title:
--   Polynomial form of an injective rational homomorphism
-- statement:
--   Let $F$ be a field, $k$ an algebraically closed field equipped with an $F$-algebra structure, and let $W, W'$ be Weierstrass curves over $F$, each assumed elliptic (nonvanishing discriminant). Let $u$ be a homomorphism of additive groups from the affine Mordell–Weil-type point group $(W_k)(k)$ of the base change of $W$ to $k$ to that of $W'$, and assume two hypotheses on $u$: first, that $u$ lies in [`WeierstrassCurve.rationalHomSet k W W'`](def/WeierstrassCurve_RationalEnd.html#L28), i.e. either $u = 0$ or $u$ is rationally represented over $F$ — there exist bivariate polynomials $n_X, d_X, n_Y, d_Y \in F[X][Y]$ and a finite set $B \subseteq k$ such that for every affine point $(x,y)$ of $W_k$ (nonsingular in the sense of the Weierstrass equation) with $x \notin B$ one has $d_X(x,y) \neq 0 \neq d_Y(x,y)$ and $u(x,y)$ is the affine point with coordinates $\bigl(n_X(x,y)/d_X(x,y),\, n_Y(x,y)/d_Y(x,y)\bigr)$, the polynomials being evaluated after base change to $k$; and second, that $u$ is injective. The conclusion is that there are univariate polynomials $p_X, q_X, p_Y, q_Y \in k[X]$ and a finite set $B \subseteq k$ such that for every affine point $(x,y)$ of $W_k$ with $x \notin B$, the image $u(x,y)$ is again an affine point, with coordinates $\bigl(p_X(x) + q_X(x)\,y,\; p_Y(x) + q_Y(x)\,y\bigr)$. Note that the resulting polynomials are allowed coefficients in $k$, not merely in $F$.
--
--   This is the "regularity on the affine part" statement for an injective rational homomorphism of elliptic curves: after excluding finitely many abscissae, the coordinates of $u$ are given by polynomials in $x$ that are at most linear in $y$, reflecting that the coordinate ring of an affine Weierstrass curve is free of rank two over $k[x]$. It is the input to the results extracting a Weierstrass variable change from a rational homomorphism admitting a two-sided inverse, such as [`WeierstrassCurve.exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet`](thm.html#WeierstrassCurve.exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_polynomial_rep_of_injective_of_mem_rationalHomSet
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (u : (W.baseChange k).toAffine.Point →+ (W'.baseChange k).toAffine.Point)
    (hu : u ∈ WeierstrassCurve.rationalHomSet k W W') (hinj : Function.Injective u) :
    ∃ (pX qX pY qY : Polynomial k) (B : Set k), B.Finite ∧
      ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
        ∃ h', u (.some x y h) =
          .some (pX.eval x + qX.eval x * y) (pY.eval x + qY.eval x * y) h' := by sorry
