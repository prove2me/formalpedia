-- Prove2me | Theorems.Thm_RobustGeneralization_BernUpper_lemma24_inner_theta_lower_tail
-- name    : RobustGeneralization.BernUpper.lemma24_inner_theta_lower_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:29:37.216835+00:00
-- url     : https://prove2.me/theorems/4464b669-5ee6-4a59-92ee-0831b8e8ea79
-- title:
--   Lemma 24 — P[⟨z, θ⋆⟩ ≤ 2τd − √(2d log 1/δ)] ≤ δ in the Bernoulli model
-- statement:
--   Let $(x,y)$ be one sample of the $(\theta^\star,\tau)$-Bernoulli model with $\theta^\star\in\{\pm1\}^d$, $d\ge1$ and $0<\tau\le\tfrac12$, and let $z=xy$. For every $\delta>0$,
--   $$\mathbb P\Big[\langle z,\theta^\star\rangle\ \le\ 2\tau d-\sqrt{2d\log(1/\delta)}\Big]\ \le\ \delta .$$
--
--   The mean of $\langle z,\theta^\star\rangle$ is $2\tau d$, so the lemma is a one-sided lower-tail bound for this sum of $d$ independent bounded terms. It is the concentration step behind Lemma 25.
--
--   **Formalization Note.** The hypothesis $d\ge1$ is added: for $d=0$ the event reads $0\le0$ and has probability $1$, so the printed statement fails for $\delta<1$. For $\delta\ge1$, Lean's $\log(1/\delta)\le0$ and $\sqrt{\cdot}$ of a nonpositive number is $0$; the statement is then trivially true, as it is on the page. The bound $\tau\le\tfrac12$ makes the model a probability distribution (Definition 7 needs $\tfrac12-\tau\ge0$).
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 31, Lemma 24

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, p. 31, Lemma 24. For one sample `p = (x, y)` of the
`(θ⋆, τ)`-Bernoulli model with `θ⋆ = pm θ` and `z = xy = zvec p`, and every `δ > 0`,
`P[⟨z, θ⋆⟩ ≤ 2τd − √(2d log 1/δ)] ≤ δ`. The hypothesis `1 ≤ d` is added: at `d = 0` the event
is `0 ≤ 0` and has probability `1`. -/
theorem lemma24_inner_theta_lower_tail {d : ℕ} (hd : 1 ≤ d) (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) (δ : ℝ) (hδ : 0 < δ) :
    bprob θ τ (fun p => inner ℝ (zvec p) (pm θ)
        ≤ 2 * τ * d - Real.sqrt (2 * d * Real.log (1 / δ))) ≤ δ := by sorry

end RobustGeneralization.BernUpper
