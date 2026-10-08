-- Prove2me | Theorems.Thm_SelfScaledIPM_ShortStep_lemma_6_3
-- name    : SelfScaledIPM.ShortStep.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:44.598687+00:00
-- url     : https://prove2.me/theorems/14a2ec75-e54f-4a2f-8ca6-93eb03dde748
-- title:
--   Lemma 6.3, pp. 27–28 — if η = ϵ₊/(1 − δ) < 1 then ‖q_x‖_x, ‖q_s‖_s ≤ η, the step is strictly feasible, and (6.12) holds
-- statement:
--   Let $(x, y, s) \in N(\beta)$ with $0 < \beta < 1$, $\delta = \lambda_\infty(x,s)$, let $0 < \kappa < 1$, $\mu_+ = (1-\kappa/\sqrt\nu)\mu(x,s)$ (6.4), $\delta_+$, $\epsilon_+$ as in (6.5), $w$ the scaling point of $(x, s)$, and $(q_x, q_y, q_s)$ a solution of (6.7), with $x_+ = x - q_x$, $y_+ = y - q_y$, $s_+ = s - q_s$. Suppose
--   $$\eta := \frac{\epsilon_+}{1 - \delta} < 1.\qquad (6.11)$$
--   Then $\delta_+ \le \epsilon_+ < 1$,
--   $$\|q_x\|_x \le \eta,\qquad \|q_s\|_s \le \eta,\qquad x_+ \in S^0(P),\qquad (y_+, s_+) \in S^0(D),$$
--   and for every $v \in E$ and $u \in E^*$
--   $$\|v\|_{x_+} \le \frac{1}{1-\eta}\|v\|_x,\qquad \|u\|_{x_+} \le (1+\eta)\|u\|_x.\qquad (6.12)$$
--
--   The lemma guarantees that the short step stays strictly feasible and controls the local norms at the new point.
--
--   **Formalization Note** $\|q_x\|_x$ is `lnorm F x qx`; $\|q_s\|_s$, a dual vector at a dual point, is `lnorm F* s qs`; in (6.12) $\|v\|_{x_+}$ is `lnorm F x₊ v` and $\|u\|_{x_+}$ is `dnorm F x₊ u`. The norms at $x_+$ are asserted after strict feasibility, as the paper does. The parenthetical "$\delta_+ \le \epsilon_+ < 1$" of the page is included as a conjunct. $\kappa \in (0,1)$ and $\beta \in (0,1)$ are as in Lemma 6.2.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), pp. 27–28, Lemma 6.3, (6.11)–(6.12)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.ShortStep

/-- **Lemma 6.3** (pp. 27–28). Let `(x, y, s) ∈ N(β)`, `β ∈ (0, 1)`, `κ ∈ (0, 1)`,
`µ₊ = (1 − κ/√ν)µ(x, s)` (6.4), `w` the scaling point, `(q_x, q_y, q_s)` the solution of (6.7),
and suppose `η = ϵ₊/(1 − δ) < 1` (6.11). Then `δ₊ ≤ ϵ₊ < 1`, `‖q_x‖_x ≤ η`, `‖q_s‖_s ≤ η`,
`x₊ = x − q_x ∈ S⁰(P)`, `(y₊, s₊) = (y − q_y, s − q_s) ∈ S⁰(D)`, and for all `v ∈ E`, `u ∈ E*`:
`‖v‖_{x₊} ≤ (1 − η)⁻¹‖v‖_x`, `‖u‖_{x₊} ≤ (1 + η)‖u‖_x` (6.12). -/
theorem lemma_6_3 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (β κ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hN : InN K F A b c ν β x y s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : IsScalingPoint K F x s w)
    (qx : EuclideanSpace ℝ (Fin n)) (qy : EuclideanSpace ℝ (Fin m)) (qs : EuclideanSpace ℝ (Fin n))
    (hq : IsShortStepDir F A x s w (muPlus ν κ x s) qx qy qs)
    (hη : eta K F ν κ x s < 1) :
    let μp := muPlus ν κ x s
    let δp := absn (ConvexOptimization.dualCone K) (-gradient F x) (μp⁻¹ • s + gradient F x)
    let εp := lambda2bar F x s μp
    let η := eta K F ν κ x s
    (δp ≤ εp ∧ εp < 1) ∧
    lnorm F x qx ≤ η ∧ lnorm (conj K F) s qs ≤ η ∧
    IsPrimalStrict K A b (x - qx) ∧ IsDualStrict K A c (y - qy) (s - qs) ∧
    (∀ v : EuclideanSpace ℝ (Fin n), lnorm F (x - qx) v ≤ (1 - η)⁻¹ * lnorm F x v) ∧
    (∀ u : EuclideanSpace ℝ (Fin n), dnorm F (x - qx) u ≤ (1 + η) * dnorm F x u) := by sorry

end SelfScaledIPM.ShortStep
