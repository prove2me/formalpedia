-- Prove2me | Theorems.Thm_StatComplexityDM_LinearLB_linear_bandit_localized_dec_lower_bound
-- name    : StatComplexityDM.LinearLB.linear_bandit_localized_dec_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:20.721885+00:00
-- url     : https://prove2.me/theorems/7dc7e59b-fc1d-4567-b8a6-145c90fa972a
-- title:
--   Proposition 6.2, p. 41 — linear bandits on the unit ball: dec_γ(M^∞_{ε_γ}(M̄), M̄) ≥ d/(12γ) for d ≥ 4, γ ≥ 2d/3, at ε_γ = 2d/(3γ)
-- statement:
--   Consider the linear bandit setting with rewards in $\mathcal{R} = [-1,+1]$ and $\Pi = \Theta = \{v \in \mathbb{R}^d : \|v\|_2 \le 1\}$: the model with parameter $\theta \in \Theta$ has mean reward $f^\theta(\pi) = \langle\theta,\pi\rangle$ and outcome law $\mathrm{Rad}(\langle\theta,\pi\rangle)$ on $\{-1,+1\}$. Let $\theta \mapsto \pi_\theta$ be a maximizer selector over the ball, $g^\theta(\pi) = f^\theta(\pi_\theta) - f^\theta(\pi)$ the regret, and $\mathcal{M}^\infty_\varepsilon(\overline{M})$ the localized class (12).
--
--   For all $d \ge 4$ and $\gamma \ge 2d/3$ there is a reference model $\overline{M} \in \mathcal{M}$ such that, for every Borel probability measure $p$ on $\Pi$, some model $M \in \mathcal{M}^\infty_{\varepsilon_\gamma}(\overline{M})$ satisfies
--   $$
--   \mathbb{E}_{\pi\sim p}\Bigl[ f^M(\pi_M) - f^M(\pi) - \gamma \cdot D^2_{\mathrm{H}}\bigl(M(\pi), \overline{M}(\pi)\bigr) \Bigr] \ge \frac{d}{12\gamma}, \qquad \varepsilon_\gamma = \frac{2d}{3\gamma}.
--   $$
--   Equivalently,
--   $$
--   \mathsf{dec}_\gamma\bigl(\mathcal{M}^\infty_{\varepsilon_\gamma}(\overline{M}), \overline{M}\bigr) \ge \frac{d}{12\gamma}.
--   $$
--
--   Combined with the in-expectation lower bound of Theorem 3.2, this gives the $\Omega(\sqrt{dT})$ regret lower bound for linear bandits under Euclidean geometry.
--
--   **Formalization Note** The page prints $\varepsilon_\gamma = d/(3\gamma)$. Its proof takes $\Delta = d/(3\gamma)$ and the family $\theta_i = \Delta e_i$, whose regret functions $\Delta(1-\pi_i)$ reach $2\Delta$ at $\pi = -e_i$ while the reference regret is $0$; the family therefore lies in $\mathcal{M}^\infty_{2\Delta}(\overline{M})$, not $\mathcal{M}^\infty_{\Delta}(\overline{M})$, and the radius is stated as $2d/(3\gamma)$. The model class is restricted to $\pm1$ outcomes (Rademacher laws, identified with their parameters), which only shrinks the localized class, so the bound implies the page's. The DEC is unfolded as "for every $p$ there is a model attaining the bound", which is what the proof shows and implies the inf–sup inequality; the integrand is bounded and continuous on the compact ball, so the expectation is a genuine integral.
-- source:
--   arXiv:2112.13487v3, Proposition 6.2, p. 41 (proof App. E.1.1, pp. 100–101)

import Mathlib
import Definitions.Def_StatComplexityDM_LinearLB_Setting

namespace StatComplexityDM.LinearLB

open MeasureTheory

/-- Proposition 6.2 (arXiv:2112.13487v3, p. 41; proof pp. 100–101), with the localization radius
`ε_γ = 2d/(3γ)` that its proof supports: for `d ≥ 4` and `γ ≥ 2d/3` there is a reference model
`M̄` in the class such that, for every decision distribution `p` on the unit ball, some model in
`M^∞_{ε_γ}(M̄)` has `E_{π∼p}[g^M(π) − γ D²_H(M(π), M̄(π))] ≥ d/(12γ)`; i.e.
`dec_γ(M^∞_{ε_γ}(M̄), M̄) ≥ d/(12γ)`. -/
theorem linear_bandit_localized_dec_lower_bound (d : ℕ) (hd : 4 ≤ d) (γ : ℝ)
    (hγ : 2 * (d : ℝ) / 3 ≤ γ) (piStar : Ball d → Ball d) (hpiStar : IsBallArgmax piStar) :
    ∃ θbar : Ball d, ∀ p : ProbabilityMeasure (Ball d),
      ∃ θ ∈ linLocalized piStar θbar (2 * (d : ℝ) / (3 * γ)),
        (d : ℝ) / (12 * γ) ≤
          ∫ π, (gapLin piStar θ π - γ * hellLin θ θbar π) ∂(p : Measure (Ball d)) := by sorry

end StatComplexityDM.LinearLB
