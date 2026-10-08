-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_3_1
-- name    : SelfScaledLongStep.PrimalDual.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:21:48.369004+00:00
-- url     : https://prove2.me/theorems/47273e6b-d1db-492e-acd8-2d4c47d87a88
-- title:
--   Theorem 3.1, p. 8 — F∗′(F″(v)x) = [F″(v)]⁻¹F′(x), F∗″ formula, injectivity of v ↦ F″(v)x, and K∗ = F″(v)K
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$, and let $F_*$ be the conjugate barrier on $\operatorname{int}K^*$.
--
--   1. For all $v,x\in\operatorname{int}K$,
--   $$F_*'(F''(v)x)=[F''(v)]^{-1}F'(x),\qquad F_*''(F''(v)x)=[F''(v)]^{-1}F''(x)[F''(v)]^{-1}.\qquad(3.1)\text{–}(3.2)$$
--   2. If $v_1,v_2\in\operatorname{int}K$ and $F''(v_1)x=F''(v_2)x$ for some $x\in\operatorname{int}K$, then $v_1=v_2$.
--   3. For every $v\in\operatorname{int}K$, $K^*=F''(v)K$.
--
--   The theorem says that every Hessian of a self-scaled barrier maps the cone onto its dual, and that the Hessian at $v$ is pinned down by its value at a single interior point; it underlies the existence of scaling points and the symmetry between the primal and dual sides.
--
--   **Formalization Note** $E^*$ is identified with $E=\mathbb R^n$; $[F''(v)]^{-1}$ is `(hess F v).inverse`. The barrier is assumed nondegenerate ($F''$ positive definite on $\operatorname{int}K$), as in the published setting; for a pointed cone this follows from the other axioms. The conjugate `conj K F` is a supremum over $\operatorname{int}K$ and is evaluated here only at $F''(v)x\in\operatorname{int}K^*$. The hypothesis $\nu\ge1$ is stated as a binder; the paper derives it from pointedness (p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 8, Theorem 3.1, (3.1)–(3.2)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Theorem 3.1** (p. 8). Let `F` be a `ν`-self-scaled barrier for the self-scaled cone `K`.
(i) For all `v, x ∈ int K`: (3.1) `F*'(F''(v)x) = [F''(v)]⁻¹F'(x)` and
(3.2) `F*''(F''(v)x) = [F''(v)]⁻¹F''(x)[F''(v)]⁻¹`, where `F* = conj K F`.
(ii) If `v₁, v₂ ∈ int K` and `F''(v₁)x = F''(v₂)x` for some `x ∈ int K`, then `v₁ = v₂`.
(iii) For every `v ∈ int K`, `K* = F''(v)K`. -/
theorem theorem_3_1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν) :
    (∀ v ∈ interior K, ∀ x ∈ interior K,
      gradient (conj K F) (hess F v x) = (hess F v).inverse (gradient F x) ∧
        hess (conj K F) (hess F v x) =
          (hess F v).inverse ∘L hess F x ∘L (hess F v).inverse) ∧
    (∀ v₁ ∈ interior K, ∀ v₂ ∈ interior K,
      (∃ x ∈ interior K, hess F v₁ x = hess F v₂ x) → v₁ = v₂) ∧
    (∀ v ∈ interior K, ConvexOptimization.dualCone K = (hess F v) '' K) := by sorry

end SelfScaledLongStep.PrimalDual
