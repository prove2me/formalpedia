-- Prove2me | Theorems.Thm_RenewForward_PriceImpact_proposition_2
-- name    : RenewForward.PriceImpact.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:00.734806+00:00
-- url     : https://prove2.me/theorems/64731af1-230f-41dd-9067-47bc05f310dd
-- title:
--   Proposition 2, pp. 16–17 — if CV_ξ τ^N_ξ ≥ 27/(4N_R), E[p_s] first decreases then increases in k_W, and p_f is eventually increasing
-- statement:
--   **Renewables' price impact.** Consider the forward-spot electricity market of the Setting under its standing assumptions: independent, bounded demand $\theta$ and wind yield $\xi \in [0, 1]$ with $V(\theta) > 0$, $V(\xi) > 0$, risk aversion $\lambda > 0$, and $N_R \ge 1$ retailers. Let $CV_\xi = \sigma_\xi/\mu_\xi$ be the coefficient of variation and $\tau^N_\xi = \tau_\xi/\sigma_\xi^3$ the normalized skewness of the wind yield, and suppose $\mu_\xi > 0$ and
--   $$CV_\xi\,\tau^N_\xi \ge \zeta := \frac{27}{4N_R}.$$
--   Then:
--   1. at every wind capacity $k_W \ge 0$ a forward-spot equilibrium $(f_{P1}, f_{P2}, p_f)$ exists;
--   2. there are thresholds $\bar k^s_W > 0$ and $\bar k^f_W \ge 0$ such that, for every selection $k_W \mapsto (f_{P1}(k_W), f_{P2}(k_W), p_f(k_W))$ of equilibria on $[0, \infty)$, the expected spot price $E[p_s]$ at the equilibrium is strictly decreasing in $k_W$ on $[0, \bar k^s_W]$ and strictly increasing on $[\bar k^s_W, \infty)$, and the forward price $p_f$ is strictly increasing in $k_W$ on $[\bar k^f_W, \infty)$.
--
--   This is the paper's main finding: once forward hedging is accounted for, adding low-cost but variable and positively skewed wind capacity eventually raises expected spot and forward prices, reversing the merit-order effect.
--
--   **Formalization Note.** The page asserts "there exists a threshold $\zeta > 0$"; the value $\zeta = 27/(4N_R)$ is taken from the proof (p. 37), which implies the existential form. "Decreasing" and "increasing" are read strictly, on closed intervals, which is stronger than the page's "for $k_W < \bar k^s_W$" and "for $k_W \ge \bar k^s_W$"; $\bar k^s_W > 0$ excludes an empty decreasing phase. $E[p_s]$ is the integral of the Lemma 1 spot price at the equilibrium forward sales. The hypothesis $\mu_\xi > 0$ is implied by $\xi \in [0, 1]$ and $V(\xi) > 0$ and is stated for readability. The inverse demand is linear on all of $k_W \ge 0$ (Assumption 1); the turning point may lie where Assumption 1 fails for some realizations. The footnote conditions $N_R > 6$ and $c \le \min\{p_R, a\}$ are not assumed, which makes the statement stronger than with them.
-- source:
--   Peura & Bunn, Renewable power and electricity prices: The impact of forward markets, author-accepted manuscript, LBS Research Online eprint 1432 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3710), pp. 16–17, Proposition 2; ζ from the proof of Proposition 2, p. 37

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting

namespace RenewForward.PriceImpact

open MeasureTheory ProbabilityTheory

/-- Proposition 2 (Renewables' price impact), pp. 16–17, with `ζ = 27/(4N_R)` (proof, p. 37): if
`CV_ξ τ^N_ξ ≥ ζ`, the forward-spot equilibrium exists at every capacity `kW ≥ 0`, the expected spot price is
strictly decreasing on `[0, k̄^s_W]` and strictly increasing on `[k̄^s_W, ∞)`, and the forward price is strictly
increasing on `[k̄^f_W, ∞)`, along every equilibrium selection. -/
theorem proposition_2 (M : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (θ ξ : Ω → ℝ) (hS : Standing M P θ ξ)
    (hmu : 0 < muXi P ξ)
    (hζ : 27 / (4 * (M.NR : ℝ)) ≤ cvXi P ξ * tauNXi P ξ) :
    (∀ kW : ℝ, 0 ≤ kW → ∃ f1 f2 pf : ℝ, IsFwdEq M P θ ξ kW f1 f2 pf) ∧
    ∃ ks kf : ℝ, 0 < ks ∧ 0 ≤ kf ∧
      ∀ e : ℝ → ℝ × ℝ × ℝ,
        (∀ kW : ℝ, 0 ≤ kW → IsFwdEq M P θ ξ kW (e kW).1 (e kW).2.1 (e kW).2.2) →
        StrictAntiOn (fun kW => ∫ w, spotP M θ ξ kW ((e kW).1 + (e kW).2.1) w ∂P) (Set.Icc 0 ks) ∧
        StrictMonoOn (fun kW => ∫ w, spotP M θ ξ kW ((e kW).1 + (e kW).2.1) w ∂P) (Set.Ici ks) ∧
        StrictMonoOn (fun kW => (e kW).2.2) (Set.Ici kf) := by sorry

end RenewForward.PriceImpact
