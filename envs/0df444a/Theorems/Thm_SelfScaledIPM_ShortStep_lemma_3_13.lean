-- Prove2me | Theorems.Thm_SelfScaledIPM_ShortStep_lemma_3_13
-- name    : SelfScaledIPM.ShortStep.lemma_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:38.622141+00:00
-- url     : https://prove2.me/theorems/2c9231e4-8e35-479b-b4cf-e7bf4075e427
-- title:
--   Lemma 3.13, p. 13 — (1 − δ)F″(x) ≤ F″(w)/µ ≤ (1 + δ)F″(x) and (1 − δ)F∗″(s) ≤ F∗″(t)/µ ≤ (1 + δ)F∗″(s) when δ = |s/µ + F′(x)|_x < 1
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$ and conjugate $F_*$. Let $x \in \operatorname{int} K$, $s \in \operatorname{int} K^*$, let $w \in \operatorname{int} K$ be the scaling point, $F''(w)x = s$, and put $t = -F'(w)$. Suppose that for some $\mu > 0$
--   $$\delta := \Big|\tfrac{1}{\mu}s + F'(x)\Big|_x < 1 .$$
--   Then, in the order of quadratic forms,
--   $$(1-\delta)F''(x) \preceq \tfrac{1}{\mu}F''(w) \preceq (1+\delta)F''(x),\qquad (1-\delta)F_*''(s) \preceq \tfrac{1}{\mu}F_*''(t) \preceq (1+\delta)F_*''(s).\qquad (3.22)$$
--
--   The lemma says that, close to the central path, the scaling-point Hessian is a good approximation of the Hessians at the iterates themselves; it is the basic estimate behind the analysis of the short-step method.
--
--   **Formalization Note** The operator inequalities are stated pointwise, $\langle A v, v\rangle \le \langle B v, v\rangle$ for every $v$. The measure $|\cdot|_x$ of the dual vector $s/\mu + F'(x)$ is `absn K* (-F'(x))`. The point $t = -F'(w)$ lies in $\operatorname{int} K^*$ by (2.12), so $F_*$ is evaluated only in the interior of $K^*$.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 13, Lemma 3.13, (3.22); t := −F′(w) from the paragraph before the lemma

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.ShortStep

/-- **Lemma 3.13** (p. 13). Let `x ∈ int K`, `s ∈ int K*`, `w` the scaling point
(`F''(w)x = s`), `t = −F'(w)`, and `µ > 0` with `δ = |s/µ + F'(x)|_x < 1`. Then, in the
quadratic-form order, `(1 − δ)F''(x) ≤ F''(w)/µ ≤ (1 + δ)F''(x)` and
`(1 − δ)F*''(s) ≤ F*''(t)/µ ≤ (1 + δ)F*''(s)` (3.22). -/
theorem lemma_3_13 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x s w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) (hw : IsScalingPoint K F x s w)
    (μ : ℝ) (hμ : 0 < μ)
    (hδ : absn (ConvexOptimization.dualCone K) (-gradient F x) (μ⁻¹ • s + gradient F x) < 1) :
    let δ := absn (ConvexOptimization.dualCone K) (-gradient F x) (μ⁻¹ • s + gradient F x)
    let t := -gradient F w
    (∀ v : EuclideanSpace ℝ (Fin n),
      (1 - δ) * ⟪hess F x v, v⟫_ℝ ≤ ⟪hess F w v, v⟫_ℝ / μ ∧
        ⟪hess F w v, v⟫_ℝ / μ ≤ (1 + δ) * ⟪hess F x v, v⟫_ℝ) ∧
    (∀ v : EuclideanSpace ℝ (Fin n),
      (1 - δ) * ⟪hess (conj K F) s v, v⟫_ℝ ≤ ⟪hess (conj K F) t v, v⟫_ℝ / μ ∧
        ⟪hess (conj K F) t v, v⟫_ℝ / μ ≤ (1 + δ) * ⟪hess (conj K F) s v, v⟫_ℝ) := by sorry

end SelfScaledIPM.ShortStep
