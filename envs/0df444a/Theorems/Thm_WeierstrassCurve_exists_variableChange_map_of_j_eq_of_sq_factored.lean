-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored
-- name    : WeierstrassCurve.exists_variableChange_map_of_j_eq_of_sq_factored
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/1ebd7a87-e0f7-58c5-aacd-dbf547543b18
-- title:
--   Factored twist comparison for curves with equal j
-- statement:
--   Let $K$ and $L$ be fields, $f : K \to L$ a ring homomorphism, and assume $2 \neq 0$ and $3 \neq 0$ in $K$. Let $E$ and $E'$ be Weierstrass curves over $K$, both elliptic (invertible discriminant), with equal $j$-invariants $j(E) = j(E')$, this common value being neither $0$ nor $1728$. Let $s \in L$ satisfy $s^{2} = f\bigl(c_6(E)\,c_4(E') / (c_6(E')\,c_4(E))\bigr)$. The conclusion asserts that $s \neq 0$ and that there are variable changes $A, B$ over $K$, i.e. tuples $(u,r,s,t)$ with $u$ a unit acting on Weierstrass coefficients by $(x,y) \mapsto (u^{2}x + r,\ u^{3}y + u^{2}sx + t)$, such that the product in the variable-change group of $L$ of the base change $A$ along $f$, the pure scaling $(s,0,0,0)$ with $s$ viewed as a unit of $L$, and the base change of $B$ along $f$, in that order, carries $E$ base changed along $f$ to $E'$ base changed along $f$.
--
--   This is the explicit-factorisation form of the comparison of two elliptic curves with the same $j$-invariant outside $\{0,1728\}$: they become isomorphic over any extension in which the twist parameter $c_6(E)c_4(E')/(c_6(E')c_4(E))$ acquires a square root (Silverman, AEC III.1.4(b)), and here the isomorphism is produced as a product of two $K$-rational variable changes with a single scaling by $s$ in between. The factored shape is what makes the Galois behaviour of the isomorphism computable from that of $s$ alone, and it is used in [`WeierstrassCurve.exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer`](thm.html#WeierstrassCurve.exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve

theorem exists_variableChange_map_of_j_eq_of_sq_factored
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
    (heq : E.j = E'.j) (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728)
    {s : L} (hs : s ^ 2 = f (E.c₆ * E'.c₄ / (E'.c₆ * E.c₄))) :
    ∃ (A B : VariableChange K) (hs0 : s ≠ 0),
      ((A.map f) * (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange L) * (B.map f)) • E.map f
        = E'.map f := by sorry
