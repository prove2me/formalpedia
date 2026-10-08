-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_5_1
-- name    : SelfScaledLongStep.PrimalDual.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:41.084621+00:00
-- url     : https://prove2.me/theorems/49b2e3b7-8167-4cb3-9536-47e4b6089151
-- title:
--   Theorem 5.1, p. 20 — F(w + αv + βz) = F(w + αv) + F(w + βz) − F(w) along orthogonal boundary directions, with (5.4)–(5.5)
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$. Fix $v\in\partial K$, $v\ne0$, $w\in\operatorname{int}K$ and $z\in\partial K$ with $\langle F''(w)v,z\rangle=0$. For every $x=w+\alpha v+\beta z$ with $\alpha,\beta\ge0$:
--   $$F(x)=F(w+\alpha v)+F(w+\beta z)-F(w),\qquad(5.3)$$
--   $$\langle F'(x),v\rangle=\langle F'(w+\alpha v),v\rangle,\qquad\langle F'(x),z\rangle=\langle F'(w+\beta z),z\rangle,\qquad(5.4)$$
--   $$\langle F''(x)v,v\rangle=\langle F''(w+\alpha v)v,v\rangle,\quad\langle F''(x)v,z\rangle=0,\quad\langle F''(x)z,z\rangle=\langle F''(w+\beta z)z,z\rangle.\qquad(5.5)$$
--
--   The barrier is thus separable on the two-dimensional cone through $w$ spanned by orthogonal boundary directions; this structure yields the key inequality (Theorem 5.2) of the primal-dual analysis.
--
--   **Formalization Note** $F'(x)$ is `gradient F x` and $F''(x)$ is `hess F x`, with $E^*\cong E=\mathbb R^n$. The standing hypotheses of §5 (the choice of $v$, $w$, $z$) are binders. The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 20, Theorem 5.1, (5.3)–(5.5); standing hypotheses p. 19

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Theorem 5.1** (p. 20), with the standing hypotheses of §5: `v ∈ ∂K`, `v ≠ 0`, `w ∈ int K`,
`z ∈ ∂K` with `⟨F''(w)v, z⟩ = 0`. For every `x = w + αv + βz` with `α, β ≥ 0`:
(5.3) `F(x) = F(w + αv) + F(w + βz) − F(w)`;
(5.4) `⟨F'(x), v⟩ = ⟨F'(w + αv), v⟩`, `⟨F'(x), z⟩ = ⟨F'(w + βz), z⟩`;
(5.5) `⟨F''(x)v, v⟩ = ⟨F''(w + αv)v, v⟩`, `⟨F''(x)v, z⟩ = 0`, `⟨F''(x)z, z⟩ = ⟨F''(w + βz)z, z⟩`. -/
theorem theorem_5_1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (v w z : EuclideanSpace ℝ (Fin n)) (hv : v ∈ frontier K) (hv0 : v ≠ 0)
    (hw : w ∈ interior K) (hz : z ∈ frontier K) (horth : ⟪hess F w v, z⟫_ℝ = 0)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    F (w + α • v + β • z) = F (w + α • v) + F (w + β • z) - F w ∧
      ⟪gradient F (w + α • v + β • z), v⟫_ℝ = ⟪gradient F (w + α • v), v⟫_ℝ ∧
      ⟪gradient F (w + α • v + β • z), z⟫_ℝ = ⟪gradient F (w + β • z), z⟫_ℝ ∧
      ⟪hess F (w + α • v + β • z) v, v⟫_ℝ = ⟪hess F (w + α • v) v, v⟫_ℝ ∧
      ⟪hess F (w + α • v + β • z) v, z⟫_ℝ = 0 ∧
      ⟪hess F (w + α • v + β • z) z, z⟫_ℝ = ⟪hess F (w + β • z) z, z⟫_ℝ := by sorry

end SelfScaledLongStep.PrimalDual
