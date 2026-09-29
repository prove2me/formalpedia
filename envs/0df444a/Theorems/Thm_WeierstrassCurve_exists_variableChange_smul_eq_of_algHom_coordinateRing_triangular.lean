-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular
-- name    : WeierstrassCurve.exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/5fd6032d-4a78-51d7-acd5-e77241b3e44f
-- title:
--   Triangular coordinate-ring maps come from variable changes
-- statement:
--   Let $T$ be a commutative ring and let $W$, $W'$ be Weierstrass curves over $T$. Write $T[W]$ for the affine coordinate ring `W.toAffine.CoordinateRing`, the quotient of $T[X][Y]$ by the Weierstrass polynomial of $W$, and let `WeierstrassCurve.Affine.CoordinateRing.mk W` denote the quotient map; thus the class of `C X` is the coordinate $x$ and the class of `X` is the coordinate $y$. Let $g : T[W] \to T[W']$ be a homomorphism of $T$-algebras, let $v_1, v_2 \in T^\times$ be units and $r, s', t \in T$, and assume that $g$ is triangular with these data, in the sense that $g(x) = v_1 x' + r$ and $g(y) = v_2 y' + s' x' + t$ in $T[W']$, where $x', y'$ are the coordinates of $W'$, the coefficients act by scalar multiplication and the constants $r$, $t$ are images under the structure map $T \to T[W']$. Then there exists a variable change $C = (u, r_C, s_C, t_C)$ over $T$, i.e. a term of `WeierstrassCurve.VariableChange T` with $u \in T^\times$, such that $C \bullet W = W'$ and moreover $u^2 = v_1$, $u^3 = v_2$, $r_C = r$, $u^2 s_C = s'$ and $t_C = t$.
--
--   This is the ring-theoretic form, over an arbitrary commutative ring, of the classical statement that the only isomorphisms between Weierstrass models are the substitutions $(x,y) \mapsto (u^2x + r,\ u^3y + u^2sx + t)$: a $T$-algebra map of coordinate rings which is triangular for the filtration by $x$- and $y$-degrees, with units on the diagonal, is induced by such a variable change, and the parameters of that change are read off from the given coefficients. It is used in the comparison of isomorphisms of projective Weierstrass models with variable changes over Artinian rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem WeierstrassCurve.exists_variableChange_smul_eq_of_algHom_coordinateRing_triangular
    (T : Type) [CommRing T] (W W' : WeierstrassCurve T)
    (g : W.toAffine.CoordinateRing →ₐ[T] W'.toAffine.CoordinateRing)
    (v₁ v₂ : Tˣ) (r s' t : T)
    (hx : g (WeierstrassCurve.Affine.CoordinateRing.mk W (C X)) =
      (v₁ : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ r)
    (hy : g (WeierstrassCurve.Affine.CoordinateRing.mk W X) =
      (v₂ : T) • WeierstrassCurve.Affine.CoordinateRing.mk W' X +
        s' • WeierstrassCurve.Affine.CoordinateRing.mk W' (C X) + algebraMap T _ t) :
    ∃ C : WeierstrassCurve.VariableChange T,
      C • W = W' ∧ ((C.u : T) ^ 2 = v₁ ∧ (C.u : T) ^ 3 = v₂) ∧ C.r = r ∧ (C.u : T) ^ 2 * C.s = s' ∧ C.t = t := by sorry
