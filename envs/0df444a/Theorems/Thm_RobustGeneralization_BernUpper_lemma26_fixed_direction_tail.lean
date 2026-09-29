-- Prove2me | Theorems.Thm_RobustGeneralization_BernUpper_lemma26_fixed_direction_tail
-- name    : RobustGeneralization.BernUpper.lemma26_fixed_direction_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:30:38.225074+00:00
-- url     : https://prove2.me/theorems/e6b1e9d3-87c2-49bb-9ec9-b9b18115b296
-- title:
--   Lemma 26 — for a unit w with ⟨w, 2τθ⋆⟩ ≥ 0, P[⟨w, z⟩ ≤ 0] ≤ exp(−2τ²⟨w, θ⋆⟩²)
-- statement:
--   Let $(x,y)$ be one sample of the $(\theta^\star,\tau)$-Bernoulli model with $\theta^\star\in\{\pm1\}^d$ and $0<\tau\le\tfrac12$, and let $z=xy$. Let $w\in\mathbb R^d$ be a fixed vector with $\|w\|_2=1$ and $\langle w,2\tau\theta^\star\rangle\ge0$. Then
--   $$\mathbb P\big[\langle w,z\rangle\le0\big]\ \le\ \exp\!\big(-2\tau^2\langle w,\theta^\star\rangle^2\big).$$
--
--   Since a fresh sample is misclassified by $f_w$ only if $\langle w,z\rangle\le0$, the lemma bounds the classification error of any fixed linear classifier in terms of its alignment with $\theta^\star$.
--
--   **Formalization Note.** $w$ does not depend on the sample. $\tau\le\tfrac12$ is the standing restriction that makes the model a probability distribution.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 32, Lemma 26

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, p. 32, Lemma 26. For one sample `p = (x, y)` of the
`(θ⋆, τ)`-Bernoulli model with `θ⋆ = pm θ`, `z = xy = zvec p`, and any fixed unit vector `w`
(Euclidean norm `1`) with `⟨w, 2τθ⋆⟩ ≥ 0`, `P[⟨w, z⟩ ≤ 0] ≤ exp(−2τ²⟨w, θ⋆⟩²)`. -/
theorem lemma26_fixed_direction_tail {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) (w : E d) (hw : ‖w‖ = 1)
    (hwθ : 0 ≤ inner ℝ w ((2 * τ) • pm θ)) :
    bprob θ τ (fun p => inner ℝ w (zvec p) ≤ 0)
      ≤ Real.exp (-(2 * τ ^ 2 * (inner ℝ w (pm θ)) ^ 2)) := by sorry

end RobustGeneralization.BernUpper
