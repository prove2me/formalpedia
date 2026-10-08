-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_corollary_3_2
-- name    : SelfScaledLongStep.PrimalDual.corollary_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:22.054687+00:00
-- url     : https://prove2.me/theorems/716e9a22-ae61-4cbd-8532-92ea229a0d5b
-- title:
--   Corollary 3.2 (i)–(ii), pp. 11–12 — F‴(x)[v] ⪯ 0 for v ∈ K, and F‴(x)[p] ⪯ 2F″(x) when x + p ∈ K
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$. Write $F'''(x)[p]$ for the derivative of the Hessian $F''$ at $x$ in the direction $p$, a self-adjoint operator; operator inequalities are in the positive semidefinite order.
--
--   1. For every $v\in K$ and $x\in\operatorname{int}K$, the operator $F'''(x)[v]$ is negative semidefinite.
--   2. If $x\in\operatorname{int}K$ and $x+p\in K$, then
--   $$F'''(x)[p]\preceq 2F''(x).\qquad(3.4)$$
--
--   These bounds on the third derivative are what drive the global Hessian estimates of §4 (Theorem 4.1), which hold up to the boundary of the cone rather than only in a Dikin ellipsoid.
--
--   **Formalization Note** $F'''(x)[p]$ is `fderiv ℝ (hess F) x p`; both inequalities are stated as quadratic forms: $\langle F'''(x)[v]u,u\rangle\le0$ and $\langle F'''(x)[p]u,u\rangle\le2\langle F''(x)u,u\rangle$ for every $u$. $F$ is $C^3$ on $\operatorname{int}K$ by self-concordance, so no smoothness hypothesis is added. Parts (iii)–(iv) of the corollary are not stated. The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, pp. 11–12, Corollary 3.2 (i)–(ii), (3.4)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Corollary 3.2 (i)–(ii)** (pp. 11–12). Write `F'''(x)[p]` for the derivative of the Hessian
`F''` at `x` in the direction `p` (`fderiv ℝ (hess F) x p`, a linear map `E → E`); operator
inequalities are in the positive semidefinite order, i.e. as quadratic forms.
(i) For `v ∈ K` and `x ∈ int K`, `F'''(x)[v]` is negative semidefinite.
(ii) (3.4) If `x ∈ int K` and `x + p ∈ K`, then `F'''(x)[p] ≤ 2F''(x)`. -/
theorem corollary_3_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν) :
    (∀ v ∈ K, ∀ x ∈ interior K, ∀ u : EuclideanSpace ℝ (Fin n),
      ⟪fderiv ℝ (hess F) x v u, u⟫_ℝ ≤ 0) ∧
    (∀ x ∈ interior K, ∀ p : EuclideanSpace ℝ (Fin n), x + p ∈ K →
      ∀ u : EuclideanSpace ℝ (Fin n),
        ⟪fderiv ℝ (hess F) x p u, u⟫_ℝ ≤ 2 * ⟪hess F x u, u⟫_ℝ) := by sorry

end SelfScaledLongStep.PrimalDual
