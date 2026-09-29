-- Prove2me | Theorems.Thm_RobustGeneralization_BernUpper_corollary28_single_sample_error_beta
-- name    : RobustGeneralization.BernUpper.corollary28_single_sample_error_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:31:35.215305+00:00
-- url     : https://prove2.me/theorems/ccfc7c7b-314f-435e-9aed-597be0d12638
-- title:
--   Corollary 28 — if τ ≥ (log(1/β)/2d)^{1/4}, then w.p. ≥ 1 − exp(−τ²d/2) f_ŵ has classification error ≤ β
-- statement:
--   Let $\beta>0$, let $\theta^\star\in\{\pm1\}^d$, and let $0<\tau\le\tfrac12$ satisfy
--   $$\tau\ \ge\ \Big(\frac{\log(1/\beta)}{2d}\Big)^{1/4}.$$
--   Let $(x,y)$ be one training sample of the $(\theta^\star,\tau)$-Bernoulli model and $\hat w=yx/\|x\|_2$. Then, with probability at least $1-\exp(-\tau^2d/2)$ over the training sample, the linear classifier $f_{\hat w}$ has classification error at most $\beta$ on a fresh sample of the same model.
--
--   Choosing $\beta=1/100$ gives Theorem 8 of the main text: a single sample suffices for $1\%$ standard error once $\tau\gtrsim d^{-1/4}$.
--
--   **Formalization Note.** The hypothesis $\beta>0$ is added: for $\beta\le0$ the statement is false (for $\beta=0$ Lean's $\log(1/0)=0$ removes the condition on $\tau$ while an error $\le0$ is impossible). The high-probability statement is stated through its failure event, as in Theorem 27. For $\beta\ge1$ the base of the fourth root is nonpositive and Lean's real power returns a junk value, but the conclusion holds anyway because an error never exceeds $1$. For $d=0$, Lean's division by $0$ makes the condition $\tau\ge0$, and the failure bound is $\exp(0)=1$. $\tau\le\tfrac12$ is the standing restriction that makes the model a probability distribution.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 33, Corollary 28

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, p. 33, Corollary 28. If `τ ≥ (log(1/β) / (2d))^{1/4}`, then
for one training sample `p = (x, y)` of the `(θ⋆, τ)`-Bernoulli model and the unit vector
`ŵ = yx / ‖x‖₂`, with probability at least `1 − exp(−τ²d/2)` the linear classifier `f_ŵ` has
classification error at most `β`; stated as a bound on the probability of the failure event.
The hypothesis `0 < β` is added (at `β ≤ 0` the statement is false). -/
theorem corollary28_single_sample_error_beta {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) (β : ℝ) (hβ : 0 < β)
    (hτβ : (Real.log (1 / β) / (2 * d)) ^ ((1 : ℝ) / 4) ≤ τ) :
    bprob θ τ (fun p => β < clsErr θ τ (linClf (‖pm p.1‖⁻¹ • (lab p.2 • pm p.1))))
      ≤ Real.exp (-(τ ^ 2 * d / 2)) := by sorry

end RobustGeneralization.BernUpper
