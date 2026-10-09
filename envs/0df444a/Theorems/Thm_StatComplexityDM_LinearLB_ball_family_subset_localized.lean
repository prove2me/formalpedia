-- Prove2me | Theorems.Thm_StatComplexityDM_LinearLB_ball_family_subset_localized
-- name    : StatComplexityDM.LinearLB.ball_family_subset_localized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:35.956109+00:00
-- url     : https://prove2.me/theorems/199fd7bc-3490-49e2-aabe-3837fb01d8dc
-- title:
--   Proof of Proposition 6.2, p. 101 — the family θᵢ = Δeᵢ lies in M^∞_{2Δ}(Rad(0)) (printed: M^∞_Δ)
-- statement:
--   Let $\theta \mapsto \pi_\theta$ be a maximizer selector for $f^\theta(\pi) = \langle\theta,\pi\rangle$ over the unit ball $\mathbb{B}^d$, let $\Delta \in [0,1]$ and $\theta_i = \Delta \cdot e_i$. Then, with $\overline{M} = \mathrm{Rad}(0)$ the model of parameter $0$,
--   $$
--   \theta_i \in \mathcal{M}^\infty_{2\Delta}(\overline{M}), \quad\text{i.e.}\quad |g^{\theta_i}(\pi) - g^{0}(\pi)| \le 2\Delta \ \ \text{for all } \pi \in \mathbb{B}^d,
--   $$
--   where $g^\theta(\pi) = f^\theta(\pi_\theta) - f^\theta(\pi)$.
--
--   This places the hard family of Proposition 6.2 inside the localized class on which the DEC lower bound is taken.
--
--   **Formalization Note** The page asserts $\mathcal{M}' \subseteq \mathcal{M}^\infty_\Delta(\overline{M})$. Since $g^0 \equiv 0$ and $g^{\theta_i}(\pi) = \Delta(1 - \pi_i)$ ranges over $[0, 2\Delta]$ on the ball (the value $2\Delta$ is attained at $\pi = -e_i$), the inclusion holds at radius $2\Delta$ and fails at radius $\Delta$ for every $\Delta > 0$. The statement is therefore made at radius $2\Delta$.
-- source:
--   arXiv:2112.13487v3, proof of Proposition 6.2, App. E.1.1, p. 101

import Mathlib
import Definitions.Def_StatComplexityDM_LinearLB_Setting

namespace StatComplexityDM.LinearLB

/-- Proof of Proposition 6.2 (arXiv:2112.13487v3, p. 101), "M′ ⊆ M^∞_Δ(M̄)", at the radius `2Δ`
that the construction supports: every `θ_i = Δ·e_i` lies in `M^∞_{2Δ}(Rad(0))`. -/
theorem ball_family_subset_localized (d : ℕ) (piStar : Ball d → Ball d)
    (hpiStar : IsBallArgmax piStar) (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (i : Fin d) (θ : Ball d)
    (hθ : (θ : EuclideanSpace ℝ (Fin d)) = Δ • EuclideanSpace.single i 1) :
    θ ∈ linLocalized piStar (ballZero d) (2 * Δ) := by sorry

end StatComplexityDM.LinearLB
