-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_three
-- name    : WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/25cc07b8-01d5-5a19-8b8c-b9ef1a515dc7
-- title:
--   Quadratic relation on points for automorphisms of j=0 in characteristic 3
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $3$, let $E_0$ be a Weierstrass curve over $K$ that is elliptic, and assume $j(E_0) = 0$. Let $\alpha$ be an admissible change of variables over $K$ fixing the Weierstrass model, i.e. $\alpha \cdot E_0 = E_0$. Write $\sigma$ for the inverse of the bijection $E_0(K) \to E_0(K)$ on the points of the associated affine curve supplied by `Point.equivOfVariableChangeEq` for the equality $\alpha \cdot E_0 = E_0$; concretely, $\sigma$ is the transport of points along $\alpha$ from $E_0$ to $\alpha \cdot E_0 = E_0$. The assertion is that there exists an integer $t$ with $t \in \{-2,-1,0,1,2\}$ such that: (i) for every point $T$ of $E_0$ one has $\sigma(\sigma T) - t \cdot \sigma T + T = 0$ in the group $E_0(K)$; (ii) if $t = 2$ then $\sigma T = T$ for all $T$; and (iii) if $t = -2$ then $\sigma T = -T$ for all $T$.
--
--   This is the Cayley–Hamilton relation $\sigma^2 - t\sigma + 1 = 0$, with $t$ the trace of the automorphism and $|t| \le 2$ with equality exactly for $\pm 1$, in the case of the supersingular curve with $j = 0$ in characteristic $3$, whose automorphism group has order $12$. It is the characteristic-$3$ input to the general statement [`WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero`](thm.html#WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero), used for the analysis of automorphisms acting on points of an elliptic curve over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_three.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_three
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] [CharP K 3]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hj : E₀.j = 0)
    (α : WeierstrassCurve.VariableChange K) (hα : α • E₀ = E₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (∀ T : E₀.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm
            ((Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T)
          - t • (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T + T = 0) ∧
      (t = 2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = T) ∧
      (t = -2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = -T) := by sorry
