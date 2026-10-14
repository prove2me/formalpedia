-- Prove2me | Theorems.Thm_RobustSPA_AllDist_pointwise_regret
-- name    : RobustSPA.AllDist.pointwise_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:30.822852+00:00
-- url     : https://prove2.me/theorems/370ed8d6-3979-4d15-9303-2ebf96b17796
-- title:
--   Proof of Proposition 1, p. App-4 — pointwise regret of SPA(Φ) is v^(1) − v^(1)Φ(v^(1)) + ∫_{v^(2)}^{v^(1)} Φ(p) dp
-- statement:
--   Let $n \ge 1$ and let $\Phi$ be a reserve distribution on $\mathbb R$ that has a density $\phi$ and is supported on $[0,1]$; write $\Phi(p)$ also for its CDF. For every valuation vector $v \in [0,1]^n$, the regret of $\mathrm{SPA}(\Phi)$ at $v$ — the highest valuation minus the total payment collected — is
--   $$v^{(1)} - \mathbb E_{p \sim \Phi}\big[\max(v^{(2)}, p)\,\mathbf 1(v^{(1)} \ge p)\big] = v^{(1)} - v^{(1)}\Phi(v^{(1)}) + \int_{v^{(2)}}^{v^{(1)}} \Phi(p)\,dp,$$
--   where $v^{(1)} \ge v^{(2)}$ are the two highest valuations.
--
--   Integrating this identity over $v \sim \mathbf F$ gives the regret $R_n(\Phi, \mathbf F)$ of any second-price auction with random reserve against any joint law, which is how both the upper bound of Proposition 4 and the regret formulas of Proposition 1 are computed.
--
--   **Formalization Note** The paper's Proposition 1 assumes $\Phi$ supported on $[r^*, 1]$; the statement here assumes support in $[0,1]$, which contains every such case. The density is written as $\Phi = \phi\,dp$ with $\phi \ge 0$ measurable. The left side is $\mathrm{top}(v) - \sum_i p_i(v)$ for the mechanism $\mathrm{SPA}(\Phi)$ of the model file.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-4, Proof of Proposition 1 (first display); Proposition 1, p. 16

import Mathlib
import Definitions.Def_RobustSPA_AllDist_Setting
open MeasureTheory

namespace RobustSPA.AllDist

/-- Proof of Proposition 1, p. App-4: pointwise regret of `SPA(Φ)` for `Φ` with a density. -/
theorem pointwise_regret (n : ℕ) (hn : 0 < n) (ρ : ProbabilityMeasure ℝ) (φ : ℝ → ℝ)
    (hφ_meas : Measurable φ) (hφ_nonneg : ∀ t, 0 ≤ φ t)
    (hρ_density : (ρ : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (φ t)))
    (hρ_supp : (ρ : Measure ℝ) (Set.Icc 0 1)ᶜ = 0)
    (v : Fin n → ℝ) (hv : v ∈ cube n) :
    top v - ∑ i, (SPA (ρ : Measure ℝ)).p i v
      = top v - top v * cdfOf ρ (top v) + ∫ q in (second v)..(top v), cdfOf ρ q := by sorry

end RobustSPA.AllDist
