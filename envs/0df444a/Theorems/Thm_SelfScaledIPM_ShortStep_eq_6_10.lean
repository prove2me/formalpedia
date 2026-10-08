-- Prove2me | Theorems.Thm_SelfScaledIPM_ShortStep_eq_6_10
-- name    : SelfScaledIPM.ShortStep.eq_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:32.945987+00:00
-- url     : https://prove2.me/theorems/e7a61a2f-d0ea-440f-8a03-c61316292de8
-- title:
--   (6.10), p. 27 — the short step (6.7)–(6.9) keeps Ax₊ = b, A∗y₊ + s₊ = c and gives µ(x₊, s₊) = µ₊
-- statement:
--   Let $K$ be a self-scaled cone with $\nu$-self-scaled barrier $F$, $A : \mathbb R^n \to \mathbb R^m$ surjective, $x \in S^0(P)$ and $(y, s) \in S^0(D)$, and let $w$ be the scaling point of $(x, s)$. For a real number $\mu_+$ let $(q_x, q_y, q_s)$ solve (6.7),
--   $$F''(w)q_x + q_s = s + \mu_+F'(x),\qquad Aq_x = 0,\qquad A^*q_y + q_s = 0,$$
--   and set $x_+ = x - q_x$, $y_+ = y - q_y$, $s_+ = s - q_s$ (6.9). Then $Ax_+ = b$, $A^*y_+ + s_+ = c$, and
--   $$\mu(x_+, s_+) = \mu_+ .\qquad (6.10)$$
--
--   The new iterate thus satisfies the equality constraints and has exactly the targeted duality gap $\nu\mu_+$.
--
--   **Formalization Note** The identity is stated for every real $\mu_+$: the paper's derivation uses only $\langle q_s, q_x\rangle = 0$, the self-adjointness of $F''(w)$ and $\langle F'(x), x\rangle = -\nu$, not the value (6.4).
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 27, (6.7), (6.9) and the derivation of (6.10)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.ShortStep

/-- **(6.10)** (p. 27). Let `x ∈ S⁰(P)`, `(y, s) ∈ S⁰(D)`, `w` the scaling point of `(x, s)`, and
`(q_x, q_y, q_s)` solve (6.7) for a target `µ₊`. With `x₊ = x − q_x`, `y₊ = y − q_y`,
`s₊ = s − q_s` (6.9): `Ax₊ = b`, `A*y₊ + s₊ = c`, and `µ(x₊, s₊) = µ₊`. Stated for every real
`µ₊`; the paper's derivation does not use the value (6.4). -/
theorem eq_6_10 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hP : IsPrimalStrict K A b x) (hD : IsDualStrict K A c y s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : IsScalingPoint K F x s w) (μp : ℝ)
    (qx : EuclideanSpace ℝ (Fin n)) (qy : EuclideanSpace ℝ (Fin m)) (qs : EuclideanSpace ℝ (Fin n))
    (hq : IsShortStepDir F A x s w μp qx qy qs) :
    A (x - qx) = b ∧ ContinuousLinearMap.adjoint A (y - qy) + (s - qs) = c ∧
      mu ν (x - qx) (s - qs) = μp := by sorry

end SelfScaledIPM.ShortStep
