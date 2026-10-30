-- Prove2me | Theorems.Thm_PricingSamples_OneSampleMHR_mhr_opt_quantile
-- name    : PricingSamples.OneSampleMHR.mhr_opt_quantile
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:14.738734+00:00
-- url     : https://prove2.me/theorems/ec475948-e609-4041-b9d6-0cf4f3040368
-- title:
--   App. A.1, p. App-2 (Hartline et al. 2008) — for mhr F, the quantile at the oracle price satisfies F̄(r_F) ≥ e^{−1}
-- statement:
--   **The optimal quantile of an mhr distribution.** Let $F \in \mathcal F_1$ be a value distribution with a monotone (non-decreasing) hazard rate, density, and $0 < \mathbb E_F[v] < \infty$, and let $r_F$ be an oracle optimal price, a maximizer of $p \mapsto p\bar F(p)$ over $p \ge 0$. Then
--
--   $$\bar F(r_F) \;\ge\; e^{-1}.$$
--
--   The paper cites this fact from Hartline, Mirrokni and Sundararajan (2008) in App. A.1 (p. App-2): an mhr distribution has substantial mass above its optimal price. It is the set $Q^*_1$ of Theorem 1 (the case $\alpha = 1$ of $q^* \ge \alpha^{1/(1-\alpha)}$, whose limit as $\alpha \to 1$ is $e^{-1}$) and enters the proof of Theorem D-11 (p. App-27), where it restricts the quantile at the optimal price over which nature minimizes.
--
--   **Formalization Note** $r_F$ is any maximizer (`IsOptPrice`); for mhr laws the maximizer is unique.
--
--   Differences from the source:
--
--   - reading: Definition 2 (pp. 11–12): F admits a density f and the virtual value φ_F(v) = v − (1 − F(v))/f(v) satisfies φ_F(v′) − φ_F(v) ≥ α(v′ − v) for all v′ ≥ v in the support S_F → μ ≪ Lebesgue measure, and v ↦ Γ_α^{−1}(F̄(v)) is convex on {v ≥ 0 : F̄(v) > 0}; reason: the paper's own equivalent form, used in the proof of Lemma 2 (p. App-10, after Schweizer–Szech); it avoids evaluating an a.e.-defined density pointwise and takes the support to be an interval, as the paper's proofs do (with a gap in the support, e.g. F̄ = e^{−v} on [0,1], e^{−1} on [1,2], e^{−(v−1)} beyond, the pointwise condition holds at α = 1 but Lemma 2 fails at w = 0, w′ = 2, v = 1.5)
--   - reading: r_F := arg max_{p≥0} p F̄(p), presumed unique (p. 12) → any r ≥ 0 maximizing p ↦ p F̄(p) over [0, ∞); reason: the maximizer is unique for α > 0, so this is r_F; for α = 0 the printed arg max may be a set and the statement is applied to each of its elements
--   - encoding: a cdf F on [0, ∞) with 0 < E_F[v] < ∞ (class G, p. 11), F̄ = 1 − F → a probability measure μ on ℝ with μ((−∞, 0)) = 0, v ↦ v integrable, 0 < ∫ v dμ; F̄(p) = μ((p, ∞)); reason: same objects; F̄(p) = 1 − F(p) = P(v > p) is the strict tail
-- source:
--   Allouah, Bahamou, Besbes, Pricing with Samples, SSRN 3334650 (rev. 06/02/2021), p. App-2 (PDF p. 34), App. A.1 (citing Hartline, Mirrokni, Sundararajan 2008); used as Q*_1 in Theorem 1 (p. 24) and the proof of Theorem D-11 (p. App-27)

import Mathlib
import Definitions.Def_PricingSamples_OneSampleMHR_Setting

namespace PricingSamples.OneSampleMHR

open MeasureTheory

/-- App. A.1 (p. App-2), citing Hartline et al. (2008): for every monotone hazard rate law
`F ∈ 𝓕_1`, the quantile at an oracle optimal price is at least `e^{−1}`: `F̄(r_F) ≥ e^{−1}`. -/
theorem mhr_opt_quantile (μ : Measure ℝ) (hF : InFAlpha 1 μ) (r : ℝ) (hr : IsOptPrice μ r) :
    Real.exp (-1) ≤ ccdf μ r := by sorry

end PricingSamples.OneSampleMHR
