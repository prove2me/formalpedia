-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero
-- name    : WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/ace099f0-6108-509d-bf4a-eb5c398f8771
-- title:
--   Automorphisms of an elliptic curve satisfy a quadratic relation on points
-- statement:
--   Let $K$ be an algebraically closed field with decidable equality, let $p$ be a prime and suppose $K$ has characteristic $p$. Let $E_0$ be a Weierstrass curve over $K$ which is elliptic, and let $\alpha$ be an admissible change of variables for Weierstrass curves over $K$ fixing $E_0$, i.e. $\alpha \cdot E_0 = E_0$. Write $\sigma$ for the inverse of the bijection $E_0(K) \to E_0(K)$ obtained by transporting affine points along this equality: from the equality $\alpha \cdot E_0 = E_0$ one gets, by `Point.equivOfVariableChangeEq`, the equivalence between the points of the two sides induced by the change of variables, and $\sigma$ is its inverse. The assertion is that there exists an integer $t \in \{-2,-1,0,1,2\}$ such that, in the group of affine points of $E_0$, $$\sigma(\sigma T) - t\,\sigma T + T = 0 \qquad \text{for all } T \in E_0(K),$$ and moreover $t = 2$ implies $\sigma T = T$ for all $T$, while $t = -2$ implies $\sigma T = -T$ for all $T$.
--
--   This is the Cayley–Hamilton relation for an automorphism $\sigma$ of an elliptic curve acting on its points: $\sigma$ satisfies $X^2 - tX + 1$ for an integer trace $t$ with $|t| \le 2$, with the extreme values occurring only for $\sigma = \pm 1$. It feeds the extraction of the trace $t$ as an invariant of $\alpha$ in [`WeierstrassCurve.exists_trace_of_equivOfVariableChangeEq_symm_apply_eq_val_smul`](thm.html#WeierstrassCurve.exists_trace_of_equivOfVariableChangeEq_symm_apply_eq_val_smul), used in the analysis of automorphism groups at supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (α : WeierstrassCurve.VariableChange K) (hα : α • E₀ = E₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (∀ T : E₀.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm
            ((Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T)
          - t • (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T + T = 0) ∧
      (t = 2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = T) ∧
      (t = -2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = -T) := by sorry
