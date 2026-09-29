-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero
-- name    : WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/481e1edc-5e56-5eec-82b9-d63d470fed97
-- title:
--   Quadratic relation on points for automorphisms with j=1728
-- statement:
--   Let $K$ be an algebraically closed field in which $2 \ne 0$ and $3 \ne 0$, let $E_0$ be a Weierstrass curve over $K$ which is elliptic (invertible discriminant) with $j$-invariant equal to $1728$, and let $\alpha$ be an admissible change of variables over $K$ fixing $E_0$, i.e. $\alpha \cdot E_0 = E_0$. Write $\sigma$ for the self-map of the group $E_0(K)$ of affine points given by the inverse of the bijection `Point.equivOfVariableChangeEq hα`, the transport of points attached to the equality $\alpha \cdot E_0 = E_0$ (for a general equality $C \cdot W = V$ this is the bijection $V(K) \simeq W(K)$ obtained from `variableChangeEquiv`, which identifies the points of $C \cdot W$ with those of $W$). The assertion is that there exists an integer $t$ with $t \in \{-2,-1,0,1,2\}$ such that $\sigma(\sigma T) - t \cdot \sigma T + T = 0$ for every $T \in E_0(K)$, and moreover $t = 2$ implies $\sigma T = T$ for all $T$, while $t = -2$ implies $\sigma T = -T$ for all $T$. No uniqueness of $t$ is claimed, and $t$ is not identified with any invariant of $\alpha$.
--
--   This is the Cayley–Hamilton relation $\sigma^2 - t\sigma + 1 = 0$ on points for an automorphism $\sigma$ of an elliptic curve with $j = 1728$, where away from characteristics $2$ and $3$ the automorphism group of the short model $y^2 = x^3 + a_4x$ is $\mu_4$ acting by $(x,y) \mapsto (u^2x, u^3y)$. It is one of the two special-$j$ cases feeding the general statement [`WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero`](thm.html#WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero), which is used to compare automorphisms of a curve with their action on cyclic level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hj : E₀.j = 1728)
    (α : WeierstrassCurve.VariableChange K) (hα : α • E₀ = E₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (∀ T : E₀.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm
            ((Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T)
          - t • (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T + T = 0) ∧
      (t = 2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = T) ∧
      (t = -2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = -T) := by sorry
