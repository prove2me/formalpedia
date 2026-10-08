-- Prove2me | Theorems.Thm_SelfScaledIPM_ShortStep_lemma_6_2
-- name    : SelfScaledIPM.ShortStep.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:53.780252+00:00
-- url     : https://prove2.me/theorems/5a246c00-c119-4a22-b709-04e3dee3c4fb
-- title:
--   Lemma 6.2, p. 27 — after µ₊ = (1 − κ/√ν)µ: δ₊ ≤ ϵ₊, δ₊ ≤ (δ + κ)/(1 − κ), ϵ₊ ≤ (ϵ + κ)/(1 − κ)
-- statement:
--   Let $K$ be a self-scaled cone with $\nu$-self-scaled barrier $F$, $x \in \operatorname{int} K$, $s \in \operatorname{int} K^*$, and suppose (6.2):
--   $$\delta := \lambda_\infty(x, s) \le \epsilon := \lambda_2(x, s) \le \beta,\qquad 0 < \beta < 1 .$$
--   Let $\mu = \mu(x, s)$, fix $0 < \kappa < 1$ and put $\mu_+ = (1 - \kappa/\sqrt\nu)\mu$ (6.4). Then
--   $$\delta_+ := \Big|\tfrac{s}{\mu_+} + F'(x)\Big|_x \le \epsilon_+ := \Big\|\tfrac{s}{\mu_+} + F'(x)\Big\|_x\qquad (6.5)$$
--   and
--   $$\delta_+ \le \frac{\delta + \kappa}{1 - \kappa},\qquad \epsilon_+ \le \frac{\epsilon + \kappa}{1 - \kappa}.\qquad (6.6)$$
--
--   Decreasing the centring parameter by the factor $1 - \kappa/\sqrt\nu$ thus degrades the proximity measures only by a bounded amount; this is the first half of the short-step analysis.
--
--   **Formalization Note** The page calls $\kappa$ "some fixed constant"; $0 < \kappa < 1$ is added, as the proof divides by $1 - \kappa$. The bound $\beta \in (0,1)$ is the range given with (6.1). The inequality $\delta \le \epsilon$ in (6.2) is a theorem ((4.16)) and is not assumed. The lemma needs neither the linear constraints nor the scaling point, which are omitted.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 27, Lemma 6.2, (6.5)–(6.6), with (6.2) and (6.4) from p. 26

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.ShortStep

/-- **Lemma 6.2** (p. 27). Let `x ∈ int K`, `s ∈ int K*` satisfy (6.2): `δ = λ_∞(x, s) ≤
ϵ = λ₂(x, s) ≤ β` with `β ∈ (0, 1)`, and let `µ₊ = (1 − κ/√ν)µ(x, s)` (6.4) with `κ ∈ (0, 1)`.
Then `δ₊ = |s/µ₊ + F'(x)|_x ≤ ϵ₊ = ‖s/µ₊ + F'(x)‖_x` (6.5), `δ₊ ≤ (δ + κ)/(1 − κ)` and
`ϵ₊ ≤ (ϵ + κ)/(1 − κ)` (6.6). -/
theorem lemma_6_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (β κ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (x s : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) (hl2 : lambda2 F ν x s ≤ β) :
    let δ := lambdaInf K F ν x s
    let ε := lambda2 F ν x s
    let μp := muPlus ν κ x s
    let δp := absn (ConvexOptimization.dualCone K) (-gradient F x) (μp⁻¹ • s + gradient F x)
    let εp := lambda2bar F x s μp
    δp ≤ εp ∧ δp ≤ (δ + κ) / (1 - κ) ∧ εp ≤ (ε + κ) / (1 - κ) := by sorry

end SelfScaledIPM.ShortStep
