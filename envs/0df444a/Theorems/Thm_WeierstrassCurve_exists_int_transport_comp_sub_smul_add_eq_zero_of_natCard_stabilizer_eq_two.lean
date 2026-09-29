-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two
-- name    : WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/5e6860ed-f3f2-5c61-9278-6fece9027d0b
-- title:
--   Automorphisms of a Weierstrass model with two-element stabiliser act as pmid
-- statement:
--   Let $K$ be a field and let $E_0$ be a Weierstrass curve over $K$ which is elliptic (its discriminant is a unit). Assume the stabiliser of $E_0$ in the group `WeierstrassCurve.VariableChange K` of admissible changes of variables, acting on Weierstrass curves, has exactly two elements, and let $\alpha$ be a change of variables with $\alpha \cdot E_0 = E_0$. Write $\sigma$ for the inverse of the bijection `Point.equivOfVariableChangeEq hα`, i.e. for the transport of points of the affine model of $E_0$ to itself induced by $\alpha$ (the map built from `Point.vcInvFun`, transported along the equality $\alpha\cdot E_0=E_0$). The assertion is that there is an integer $t$ with $t \in \{-2,-1,0,1,2\}$ such that $\sigma(\sigma T) - t\,\sigma T + T = 0$ for every point $T$ of the affine model of $E_0$, and moreover $t = 2$ implies $\sigma T = T$ for all $T$, while $t = -2$ implies $\sigma T = -T$ for all $T$.
--
--   This is the statement that an automorphism of a Weierstrass model whose automorphism group has order two satisfies its characteristic polynomial $X^2 - tX + 1$ on points, with $t$ the trace; the list of admissible values $\{-2,\dots,2\}$ is the classical bound $|t|\le 2$, although under the present hypothesis only $t = \pm 2$ actually occurs, corresponding to $\sigma = \pm\mathrm{id}$. It feeds [`WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero`](thm.html#WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero), used in the bookkeeping relating automorphisms of elliptic curves to their action on level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two
    (K : Type*) [Field K] [DecidableEq K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (h2 : Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) E₀) = 2)
    (α : WeierstrassCurve.VariableChange K) (hα : α • E₀ = E₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (∀ T : E₀.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm
            ((Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T)
          - t • (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T + T = 0) ∧
      (t = 2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = T) ∧
      (t = -2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = -T) := by sorry
