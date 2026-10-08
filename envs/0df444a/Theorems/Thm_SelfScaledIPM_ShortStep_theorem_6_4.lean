-- Prove2me | Theorems.Thm_SelfScaledIPM_ShortStep_theorem_6_4
-- name    : SelfScaledIPM.ShortStep.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:42.038687+00:00
-- url     : https://prove2.me/theorems/2936bd67-b8a4-4f1c-8e1b-c8969d9d434a
-- title:
--   Theorem 6.4, p. 28 — after one short step from N(β), λ₂(x₊, s₊) = λ̄₂(x₊, s₊, µ₊) ≤ (2 + δ − κ)(ϵ + κ)²/((1 − δ)²(1 − κ)³)
-- statement:
--   Let $K$ be a self-scaled cone with $\nu$-self-scaled barrier $F$ and conjugate $F_*$, and consider the conic pair (2.1)/(2.3) with a surjective linear map $A$. Let $(x, y, s) \in N(\beta)$ for some $0 < \beta < 1$, and write (6.2)
--   $$\delta = \lambda_\infty(x, s),\qquad \epsilon = \lambda_2(x, s).$$
--   Fix $0 < \kappa < 1$, let $\mu_+ = (1 - \kappa/\sqrt\nu)\,\mu(x, s)$ (6.4), let $w$ be the scaling point of $(x, s)$, let $(q_x, q_y, q_s)$ solve the short-step system (6.7), and set $x_+ = x - q_x$, $y_+ = y - q_y$, $s_+ = s - q_s$ (6.9). Let $\epsilon_+ = \|s/\mu_+ + F'(x)\|_x$ and suppose
--   $$\eta = \frac{\epsilon_+}{1 - \delta} < 1 .$$
--   Then $x_+ \in \operatorname{int} K$, $s_+ \in \operatorname{int} K^*$, $\mu(x_+, s_+) = \mu_+$, and
--   $$\lambda_2(x_+, s_+) = \bar\lambda_2(x_+, s_+, \mu_+) = \Big\|\frac{s_+}{\mu_+} + F'(x_+)\Big\|_{x_+} \le \frac{(2 + \delta - \kappa)(\epsilon + \kappa)^2}{(1-\delta)^2(1-\kappa)^3}.\qquad (6.13)$$
--
--   This is the main estimate of the short-step primal-dual path-following method on self-scaled cones: with $\beta = 1/10$ and $\kappa = 1/15$ the right-hand side is below $1/10$, so the iterates stay in $N(1/10)$ while $\mu$ decreases by the factor $1 - (15\sqrt\nu)^{-1}$ per iteration, giving an $O(\sqrt\nu\ln(1/\varepsilon))$ iteration bound.
--
--   **Formalization Note** $E^*$ is identified with $E$; $\lambda_2$ and $\bar\lambda_2$ are the dual-space norm at $x_+$ of $s_+/\mu_+ + F'(x_+)$, and $\lambda_\infty$ is $|\cdot|_x$ with cone $K^*$ and centre $-F'(x)$. Added relative to the page: $0 < \kappa < 1$ ("some fixed constant"; the proof divides by $1-\kappa$ and needs $\mu_+ > 0$); $1 \le \nu$, which the paper derives from pointedness; and the conjunct $x_+ \in \operatorname{int} K$, $s_+ \in \operatorname{int} K^*$, proved in Lemma 6.3 and needed for $\lambda_2(x_+, s_+)$ to be meaningful. The first equation of (6.13) is stated as $\mu(x_+, s_+) = \mu_+$ together with $\lambda_2(x_+,s_+) = \bar\lambda_2(x_+,s_+,\mu_+)$; the second is the definition of $\bar\lambda_2$. Assumptions (2.4)–(2.5) are implied by the strictly feasible starting point. The search direction is any solution of (6.7); its existence is not assumed.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 28, Theorem 6.4, (6.13); notation (6.1)–(6.11) from pp. 26–27

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.ShortStep

/-- **Theorem 6.4** (p. 28). Let `(x, y, s) ∈ N(β)` with `β ∈ (0, 1)`, `δ = λ_∞(x, s)`,
`ϵ = λ₂(x, s)` (6.2), `κ ∈ (0, 1)`, `µ₊ = (1 − κ/√ν)µ(x, s)` (6.4), `w` the scaling point of
`(x, s)`, `(q_x, q_y, q_s)` a solution of (6.7), `x₊ = x − q_x`, `y₊ = y − q_y`, `s₊ = s − q_s`
(6.9), and suppose `η = ϵ₊/(1 − δ) < 1` (6.11). Then `x₊ ∈ int K`, `s₊ ∈ int K*` (from Lemma 6.3)
and (6.13): `λ₂(x₊, s₊) = λ̄₂(x₊, s₊, µ₊) = ‖s₊/µ₊ + F'(x₊)‖_{x₊} ≤
(2 + δ − κ)(ϵ + κ)²/((1 − δ)²(1 − κ)³)`; the first equation is `µ(x₊, s₊) = µ₊`. -/
theorem theorem_6_4 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
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
    let δ := lambdaInf K F ν x s
    let ε := lambda2 F ν x s
    let μp := muPlus ν κ x s
    let xp := x - qx
    let sp := s - qs
    (xp ∈ interior K ∧ sp ∈ interior (ConvexOptimization.dualCone K)) ∧
    mu ν xp sp = μp ∧
    lambda2 F ν xp sp = lambda2bar F xp sp μp ∧
    lambda2bar F xp sp μp ≤ (2 + δ - κ) * (ε + κ) ^ 2 / ((1 - δ) ^ 2 * (1 - κ) ^ 3) := by sorry

end SelfScaledIPM.ShortStep
