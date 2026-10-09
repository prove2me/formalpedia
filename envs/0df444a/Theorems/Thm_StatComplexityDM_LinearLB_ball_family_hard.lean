-- Prove2me | Theorems.Thm_StatComplexityDM_LinearLB_ball_family_hard
-- name    : StatComplexityDM.LinearLB.ball_family_hard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:20.66692+00:00
-- url     : https://prove2.me/theorems/cdc10eb9-70aa-46cc-8136-95fc51213d78
-- title:
--   Proof of Proposition 6.2, p. 100 — θᵢ = Δeᵢ: regret Δ(1 − πᵢ) and D²_H(Mᵢ(π), Rad(0)) ≤ ¾Δ²πᵢ², the regret and information properties with uᵢ(π) = πᵢ, vᵢ(π) = πᵢ²
-- statement:
--   Let $\mathbb{B}^d$ be the Euclidean unit ball of $\mathbb{R}^d$, let $\theta \mapsto \pi_\theta$ be a maximizer selector for the linear mean reward $f^\theta(\pi) = \langle \theta, \pi\rangle$ over the ball, let $\Delta \in [0, 1]$ and $i \in \{1, \dots, d\}$. Put $\theta_i = \Delta \cdot e_i$, $M_i(\pi) = \mathrm{Rad}(\langle \theta_i, \pi\rangle)$, and let $\overline{M}(\pi) = \mathrm{Rad}(0)$ be the model with parameter $0$. Then for every $\pi \in \mathbb{B}^d$:
--
--   1. (regret property, $u_i(\pi) = \pi_i$)
--   $$
--   f^{M_i}(\pi_{M_i}) - f^{M_i}(\pi) = \langle \theta_i, e_i - \pi\rangle = \Delta\,(1 - \pi_i);
--   $$
--   2. (information property, $v_i(\pi) = \pi_i^2$)
--   $$
--   D^2_{\mathrm{H}}\bigl(M_i(\pi), \overline{M}(\pi)\bigr) \le \tfrac34 \Delta^2 \pi_i^2 .
--   $$
--
--   Together with the sum bounds $\sum_i \pi_i \le d/2$ and $\sum_i \pi_i^2 \le 1$ (for $d \ge 4$), this makes $\{M_1, \dots, M_d\}$ a $(\Delta, \tfrac34\Delta^2, 0)$-family with respect to $\overline{M}$, the construction behind the lower bound $d/(12\gamma)$ of Proposition 6.2.
--
--   **Formalization Note** A parameter $\theta_i$ is passed as a point of the ball whose underlying vector equals $\Delta e_i$. The first identity uses that the selector attains $\langle\theta_i,\pi_{\theta_i}\rangle = \Delta$, which follows from the maximizer hypothesis. Here $u_i$ takes negative values, so the family satisfies Definition 5.1 only without its range conditions (see the restated Lemma 5.1 of this mission).
-- source:
--   arXiv:2112.13487v3, proof of Proposition 6.2, App. E.1.1, p. 100

import Mathlib
import Definitions.Def_StatComplexityDM_LinearLB_Setting

namespace StatComplexityDM.LinearLB

/-- Proof of Proposition 6.2 (arXiv:2112.13487v3, p. 100): the models `M_i(π) = Rad(⟨θ_i, π⟩)`,
`θ_i = Δ·e_i`, satisfy the regret property with `u_i(π) = π_i` and the information property with
`v_i(π) = π_i²` and constant `¾Δ²`, with respect to `M̄ = Rad(0)`. -/
theorem ball_family_hard (d : ℕ) (piStar : Ball d → Ball d)
    (hpiStar : IsBallArgmax piStar) (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (i : Fin d) (θ : Ball d)
    (hθ : (θ : EuclideanSpace ℝ (Fin d)) = Δ • EuclideanSpace.single i 1) :
    ∀ π : Ball d,
      gapLin piStar θ π = Δ * (1 - (π : EuclideanSpace ℝ (Fin d)) i) ∧
      hellLin θ (ballZero d) π ≤ 3 / 4 * Δ ^ 2 * ((π : EuclideanSpace ℝ (Fin d)) i) ^ 2 := by sorry

end StatComplexityDM.LinearLB
