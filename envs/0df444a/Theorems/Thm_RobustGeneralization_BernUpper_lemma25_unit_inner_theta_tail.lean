-- Prove2me | Theorems.Thm_RobustGeneralization_BernUpper_lemma25_unit_inner_theta_tail
-- name    : RobustGeneralization.BernUpper.lemma25_unit_inner_theta_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:30:04.509133+00:00
-- url     : https://prove2.me/theorems/97bf3b5d-e291-4ca8-b842-c9a7e22ef01f
-- title:
--   Lemma 25 — P[⟨ŵ, θ⋆⟩ ≤ τ√d] ≤ exp(−τ²d/2) for ŵ = z/‖z‖₂
-- statement:
--   Let $(x,y)$ be one sample of the $(\theta^\star,\tau)$-Bernoulli model with $\theta^\star\in\{\pm1\}^d$ and $0<\tau\le\tfrac12$, let $z=xy$, and let $\hat w=z/\|z\|_2$ be the unit vector in the direction of $z$. Then
--   $$\mathbb P\Big[\langle\hat w,\theta^\star\rangle\ \le\ \tau\sqrt d\Big]\ \le\ \exp\!\Big(-\frac{\tau^2 d}{2}\Big).$$
--
--   The lemma says that the direction learned from a single sample is, with high probability, well aligned with the true mean direction $\theta^\star$; Theorem 27 converts this alignment into a classification-error bound.
--
--   **Formalization Note.** $\tau\le\tfrac12$ is the standing restriction that makes the model a probability distribution. When $d=0$, $\hat w$ is $0$ in Lean and both sides equal $1$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 31, Lemma 25

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, p. 31, Lemma 25. For one sample `p = (x, y)` of the
`(θ⋆, τ)`-Bernoulli model with `θ⋆ = pm θ`, `z = xy` and the unit vector `ŵ = z / ‖z‖₂ = unitZ p`,
`P[⟨ŵ, θ⋆⟩ ≤ τ√d] ≤ exp(−τ²d/2)`. -/
theorem lemma25_unit_inner_theta_tail {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) :
    bprob θ τ (fun p => inner ℝ (unitZ p) (pm θ) ≤ τ * Real.sqrt d)
      ≤ Real.exp (-(τ ^ 2 * d / 2)) := by sorry

end RobustGeneralization.BernUpper
