-- Prove2me | Theorems.Thm_RobustGeneralization_BernUpper_theorem27_single_sample_generalization
-- name    : RobustGeneralization.BernUpper.theorem27_single_sample_generalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:31:06.620145+00:00
-- url     : https://prove2.me/theorems/d15b9967-48a6-4f7b-98be-e577d48b5d41
-- title:
--   Theorem 27 — one sample: w.p. ≥ 1 − exp(−τ²d/2), f_ŵ has classification error ≤ exp(−2τ⁴d)
-- statement:
--   Let $(x,y)$ be one training sample of the $(\theta^\star,\tau)$-Bernoulli model with $\theta^\star\in\{\pm1\}^d$ and $0<\tau\le\tfrac12$, let $z=yx$ and $\hat w=z/\|z\|_2$. Then, with probability at least $1-\exp(-\tau^2d/2)$ over the training sample, the linear classifier $f_{\hat w}$ satisfies
--   $$\mathbb P_{(x',y')}\big[f_{\hat w}(x')\neq y'\big]\ \le\ \exp(-2\tau^4 d),$$
--   where $(x',y')$ is a fresh, independent sample of the same model.
--
--   This is standard (non-adversarial) generalization from a single example: one sample suffices for a small classification error once $\tau^4 d$ is large.
--
--   **Formalization Note.** The high-probability statement is stated through its failure event: the probability, over the training sample, that the classification error exceeds $\exp(-2\tau^4 d)$ is at most $\exp(-\tau^2 d/2)$. Over a finite model this is equivalent to the printed form. On the page the training and the test sample are both called $(x,y)$; here they are distinct. $\tau\le\tfrac12$ is the standing restriction that makes the model a probability distribution.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 32, Theorem 27

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, p. 32, Theorem 27. Draw one training sample `p = (x, y)`
from the `(θ⋆, τ)`-Bernoulli model (`θ⋆ = pm θ`) and let `ŵ = z / ‖z‖₂ = unitZ p` with `z = yx`.
With probability at least `1 − exp(−τ²d/2)` over `p`, the linear classifier `f_ŵ` has
classification error (over a fresh sample) at most `exp(−2τ⁴d)`; stated as a bound on the
probability of the failure event. -/
theorem theorem27_single_sample_generalization {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) :
    bprob θ τ (fun p => Real.exp (-(2 * τ ^ 4 * d)) < clsErr θ τ (linClf (unitZ p)))
      ≤ Real.exp (-(τ ^ 2 * d / 2)) := by sorry

end RobustGeneralization.BernUpper
