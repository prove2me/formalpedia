-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_two_ne_zero
-- name    : WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_two_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/dc94856e-69aa-5c86-8db9-db2ba5e962ba
-- title:
--   Quadratic relation on points for automorphisms with j=0
-- statement:
--   Let $K$ be an algebraically closed field in which $2 \neq 0$ and $3 \neq 0$, let $E_0$ be a Weierstrass curve over $K$ which is elliptic and satisfies $j(E_0) = 0$, and let $\alpha$ be an admissible change of variables over $K$ fixing $E_0$, i.e. $\alpha \cdot E_0 = E_0$. Write $\sigma$ for the inverse of the bijection $E_0(K) \to E_0(K)$ obtained from `Point.equivOfVariableChangeEq` applied to this equality, that is, the transport of points `vcInvFun` attached to $\alpha$ on the affine model of $E_0$. The assertion is that there exists an integer $t$ with $t \in \{-2,-1,0,1,2\}$ such that, first, $\sigma(\sigma T) - t \cdot \sigma T + T = 0$ in the group $E_0(K)$ for every point $T$ of the affine model of $E_0$; second, if $t = 2$ then $\sigma T = T$ for all $T$; and third, if $t = -2$ then $\sigma T = -T$ for all $T$.
--
--   This is the Cayley–Hamilton relation $\sigma^2 - t\sigma + 1 = 0$, with $|t| \le 2$ and equality only for $\sigma = \pm 1$, for an automorphism of a Weierstrass model in the case $j = 0$, where the automorphism group of the short form $y^2 = x^3 + a_6$ is the group of sixth roots of unity. It feeds into [`WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero`](thm.html#WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero), the corresponding statement without the restriction on $j$; the proof here cites the description of the stabiliser of a short normal form with $a_4 = 0$ under variable changes, the additivity of the transport map on points, and its compatibility with conjugating the fixing variable change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_two_ne_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_two_ne_zero
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hj : E₀.j = 0)
    (α : WeierstrassCurve.VariableChange K) (hα : α • E₀ = E₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (∀ T : E₀.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm
            ((Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T)
          - t • (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T + T = 0) ∧
      (t = 2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = T) ∧
      (t = -2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = -T) := by sorry
