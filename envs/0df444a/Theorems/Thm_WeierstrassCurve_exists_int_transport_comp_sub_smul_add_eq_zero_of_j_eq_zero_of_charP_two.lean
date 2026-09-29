-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_two
-- name    : WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/61b9f1f1-1a01-5c0c-89dd-c44e7db2df1d
-- title:
--   Automorphisms of the j=0 curve in characteristic 2 satisfy a quadratic
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $2$, let $E_0$ be a Weierstrass curve over $K$ which is elliptic, and assume $j(E_0) = 0$. Let $\alpha$ be an admissible change of variables over $K$ fixing the model, i.e. $\alpha \cdot E_0 = E_0$. Write $\varphi$ for the inverse direction of the bijection `Point.equivOfVariableChangeEq` attached to this equality, that is the transport of points $E_0(K) \to E_0(K)$ given by `Point.vcInvFun` for $\alpha$ (here `equivOfVariableChangeEq` is obtained from the bijection `variableChangeEquiv` between the points of $\alpha \cdot E_0$ and those of $E_0$, whose forward map is `vcFun` and whose inverse is `vcInvFun`, after rewriting along $\alpha \cdot E_0 = E_0$). The assertion is the existence of an integer $t$ with $t \in \{-2,-1,0,1,2\}$ such that: $\varphi(\varphi(T)) - t \cdot \varphi(T) + T = 0$ in the group of affine points of $E_0$ for every $T$; if $t = 2$ then $\varphi(T) = T$ for all $T$; and if $t = -2$ then $\varphi(T) = -T$ for all $T$. No additivity of $\varphi$ is asserted, only these pointwise identities.
--
--   This is the Cayley–Hamilton relation for an automorphism of an elliptic curve, in the form $\varphi^2 - t\varphi + 1 = 0$ with $|t| \le 2$ and equality only for $\varphi = \pm 1$, proved here in the one characteristic-$2$ case where the automorphism group is larger than $\{\pm 1\}$, namely $j = 0$, whose automorphism group has order $24$. It feeds the general statement [`WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero`](thm.html#WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero), which provides the quadratic relation satisfied by the transport of points along an automorphism of a Weierstrass model over any algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_two.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_two
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] [CharP K 2]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hj : E₀.j = 0)
    (α : WeierstrassCurve.VariableChange K) (hα : α • E₀ = E₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (∀ T : E₀.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm
            ((Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T)
          - t • (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T + T = 0) ∧
      (t = 2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = T) ∧
      (t = -2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = -T) := by sorry
