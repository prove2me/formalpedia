-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv
-- name    : WeierstrassCurve.exists_variableChange_smul_eq_of_functionField_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/43cf87a3-fbae-5704-ae4d-288153c9f778
-- title:
--   Function field isomorphism respecting infinity comes from a variable change
-- statement:
--   Let $F$ be a field and let $W_1,W_2$ be Weierstrass curves over $F$, with $W_1$'s affine coordinate ring $F[W_1]$ assumed to be a Dedekind domain. Write $x_i$ for the class of the polynomial $C\,X$ and $y_i$ for the class of $X$ in the coordinate ring of the affine curve $W_i$, viewed inside the function field $F(W_i)$. Let $e : F(W_2) \to F(W_1)$ be an isomorphism of $F$-algebras, and let $v_\infty$ denote the valuation of $F(W_1)$ with values in $\mathbb{Z}^{m0} = \mathrm{WithZero}(\mathrm{Multiplicative}\ \mathbb{Z})$ obtained by extending to the fraction field the valuation sending a nonzero $f \in F[W_1]$ to $\exp\big(\deg_{F[X]} N(f)\big)$, $N$ the algebra norm of $F[W_1]$ over $F[X]$ (and $0$ to $0$). Assume $v_\infty(e(x_2)) \not\le 1$, i.e. $e(x_2)$ has a pole at the place at infinity of $W_1$. Then there exists a Weierstrass variable change $C = (u,r,s,t)$ over $F$, with $u$ a unit, such that $C \bullet W_2 = W_1$ and, in $F(W_1)$, $e(x_2) = u^2 x_1 + r$ and $e(y_2) = u^3 y_1 + u^2 s\, x_1 + t$, the scalars being taken along the structure map $F \to F(W_1)$.
--
--   This is the function-field form of the classical statement that two Weierstrass models of an elliptic curve differ by an admissible change of coordinates $x = u^2x' + r$, $y = u^3y' + u^2sx' + t$ (Silverman, Proposition III.3.1(b)), formulated for an abstract $F$-algebra isomorphism of function fields together with the requirement that it match the two points at infinity; the hypothesis on $e(x_2)$ is needed, since translations give $F$-automorphisms of a function field moving the point at infinity. It is used in [`WeierstrassCurve.Affine.exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv`](thm.html#WeierstrassCurve.Affine.exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv), and the proof invokes [`WeierstrassCurve.Affine.FunctionField.eq_valuationSubring_of_X_not_mem`](thm.html#WeierstrassCurve.Affine.FunctionField.eq_valuationSubring_of_X_not_mem) to identify the valuation subring transported by $e$ with the one at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv.lean

import Mathlib
import Definitions.Def_EllipticCurve_ValuationInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_variableChange_smul_eq_of_functionField_algEquiv
    {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F}
    [IsDedekindDomain W₁.toAffine.CoordinateRing]
    (e : W₂.toAffine.FunctionField ≃ₐ[F] W₁.toAffine.FunctionField)
    (hinf : ¬ WeierstrassCurve.Affine.valuationInfty W₁.toAffine
      (e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine (Polynomial.C Polynomial.X)))) ≤ 1) :
    ∃ C : WeierstrassCurve.VariableChange F, C • W₂ = W₁ ∧
      e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine (Polynomial.C Polynomial.X)))
        = algebraMap F W₁.toAffine.FunctionField ((C.u : F) ^ 2)
            * algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W₁.toAffine (Polynomial.C Polynomial.X))
          + algebraMap F W₁.toAffine.FunctionField C.r ∧
      e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine Polynomial.X))
        = algebraMap F W₁.toAffine.FunctionField ((C.u : F) ^ 3)
            * algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W₁.toAffine Polynomial.X)
          + algebraMap F W₁.toAffine.FunctionField ((C.u : F) ^ 2 * C.s)
            * algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W₁.toAffine (Polynomial.C Polynomial.X))
          + algebraMap F W₁.toAffine.FunctionField C.t := by sorry
