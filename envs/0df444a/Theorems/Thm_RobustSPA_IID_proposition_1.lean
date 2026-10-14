-- Prove2me | Theorems.Thm_RobustSPA_IID_proposition_1
-- name    : RobustSPA.IID.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:07.111928+00:00
-- url     : https://prove2.me/theorems/7c6ec621-fb58-4954-936a-3bfe65a867a3
-- title:
--   Proposition 1, p. 16 — regret of SPA(Φ) for Φ with a density on [r*, 1]: (Regret-F) for joint laws and for i.i.d. laws
-- statement:
--   Let $n \ge 1$, $r \in [0,1]$, and let the reserve distribution $\Phi$ have a density $\phi \ge 0$ vanishing outside $[r,1]$; write $\Phi(v)$ also for its CDF. Let $R_n(\Phi, F)$ be the regret of the second-price auction with random reserve $\mathrm{SPA}(\Phi)$ under the valuation distribution $F$.
--
--   1. (Regret-$\boldsymbol F$) For every distribution $F$ on $[0,1]^n$, with $F^{(1)}_n(p) = \Pr_F(v^{(1)} \le p)$ and $F^{(2)}_n(p) = \Pr_F(v^{(2)} \le p)$ the CDFs of the highest and second-highest valuations,
--   $$R_n(\Phi, F) = r - \int_0^{r} F^{(1)}_n(v)\,dv + \int_{r}^1 \Big[(1 - v\phi(v) - \Phi(v))(1 - F^{(1)}_n(v)) + \Phi(v)\big(F^{(2)}_n(v) - F^{(1)}_n(v)\big)\Big]dv.$$
--   2. (Regret-$F$) If $F = G^{\otimes n}$ is i.i.d. with marginal $G$ on $[0,1]$ and marginal CDF $G(v)$,
--   $$R_n(\Phi, G^{\otimes n}) = r - \int_0^{r} G(v)^n\,dv + \int_{r}^1 \Big[(1 - v\phi(v) - \Phi(v))(1 - G(v)^n) + \Phi(v)\,n\,G(v)^{n-1}(1 - G(v))\Big]dv.$$
--
--   These formulas express the regret of every second-price auction with a random reserve through the CDFs of the order statistics; Step 1 of the proof of Theorem 1 bounds the i.i.d. formula pointwise.
--
--   **Formalization Note.** The page writes $v\Phi'(v)$; since $\Phi$ is only assumed to have a density, $\Phi'$ is read as the density $\phi$ (they agree almost everywhere). The third display of the proposition, (Regret-$\Phi$), is not part of this item.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 16, Proposition 1, displays (Regret-F) (joint and i.i.d.)

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

namespace RobustSPA.IID

open MeasureTheory

/-- Proposition 1 (p. 16), parts (Regret-**F**) and (Regret-F). Let the reserve law `ρ` of
`SPA(Φ)` have a density `φ` supported on `[r, 1]`, and write `Φ` for its CDF. Then for every joint
law `μ` on `[0,1]ⁿ`,
`Rₙ(Φ, μ) = r − ∫_0^r F^(1)_n + ∫_r^1 (1 − vφ(v) − Φ(v))(1 − F^(1)_n(v)) + Φ(v)(F^(2)_n(v) − F^(1)_n(v)) dv`,
and for i.i.d. valuations with marginal law `G` on `[0,1]` (CDF `F`),
`Rₙ(Φ, Gⁿ) = r − ∫_0^r Fⁿ + ∫_r^1 (1 − vφ(v) − Φ(v))(1 − F(v)ⁿ) + Φ(v) n F(v)^{n−1}(1 − F(v)) dv`. -/
theorem proposition_1 (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφ0 : ∀ v, 0 ≤ φ v)
    (hφs : ∀ v ∉ Set.Icc r 1, φ v = 0)
    (ρ : ProbabilityMeasure ℝ)
    (hρ : (ρ : Measure ℝ) = volume.withDensity (fun v => ENNReal.ofReal (φ v))) :
    (∀ μ ∈ Fall n, regret (SPA (ρ : Measure ℝ)) μ =
      r - ∫ v in (0 : ℝ)..r, F1 μ v +
        ∫ v in r..1, ((1 - v * φ v - cdfOf ρ v) * (1 - F1 μ v) +
          cdfOf ρ v * (F2 μ v - F1 μ v))) ∧
    (∀ G : ProbabilityMeasure ℝ, (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 →
      regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) =
        r - ∫ v in (0 : ℝ)..r, (cdfOf G v) ^ n +
          ∫ v in r..1, ((1 - v * φ v - cdfOf ρ v) * (1 - (cdfOf G v) ^ n) +
            cdfOf ρ v * n * (cdfOf G v) ^ (n - 1) * (1 - cdfOf G v))) := by sorry

end RobustSPA.IID
