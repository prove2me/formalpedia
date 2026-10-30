-- Prove2me | Theorems.Thm_PricingSamples_OneSampleMHR_lemma_2
-- name    : PricingSamples.OneSampleMHR.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:04.513156+00:00
-- url     : https://prove2.me/theorems/285f8735-629e-4229-830e-d4d5c9950762
-- title:
--   Lemma 2, p. 18 — single crossing: F̄ lies above the generalized Pareto interpolant G_α on [w, w′] and below it on [w′, ∞)
-- statement:
--   **Single crossing of generalized Pareto interpolants.** Fix $\alpha \in [0,1]$ and an $\alpha$-strongly regular value distribution $F \in \mathcal F_\alpha$, with complementary cdf $\bar F$ and quantiles $q_w = \bar F(w)$. Let $0 \le w < w'$. Then $\bar F$ lies above the generalized Pareto tail through $(w, q_w)$ and $(w', q_{w'})$ between the two points and below it beyond $w'$:
--
--   $$\bar F(v) \;\ge\; q_w\,\Gamma_\alpha\!\Big(\Gamma_\alpha^{-1}\big(\tfrac{q_{w'}}{q_w}\big)\frac{v-w}{w'-w}\Big)\quad (w \le v \le w'),\qquad \bar F(v) \;\le\; q_w\,\Gamma_\alpha\!\Big(\Gamma_\alpha^{-1}\big(\tfrac{q_{w'}}{q_w}\big)\frac{v-w}{w'-w}\Big)\quad (v \ge w').$$
--
--   Here $\Gamma_\alpha(v) = (1+(1-\alpha)v)^{-1/(1-\alpha)}$ for $\alpha < 1$, $\Gamma_1(v) = e^{-v}$, and $\Gamma_\alpha^{-1}(0) = +\infty$, $\Gamma_\alpha(+\infty) = 0$. For $\alpha = 1$ this says that $\log \bar F$ lies above its chord on $[w,w']$ and below the chord's extension beyond $w'$.
--
--   This is the paper's main tool for replacing an unknown tail by two of its quantiles: it gives the lower and upper envelopes used in Proposition 2 and, through it, in the dynamic programs of Propositions 3 and 4.
--
--   **Formalization Note** The interpolant is `Galpha α w q_w w' q_{w'} v` $= G_\alpha(v \mid (w,q_w),(w',q_{w'}))$, eq. (7). The case $q_{w'} = 0$ follows the paper's conventions (value $q_w$ at $v = w$, $0$ for $v > w$); when $q_w = 0$ the value is $0$.
--
--   Differences from the source:
--
--   - reading: Definition 2 (pp. 11–12): F admits a density f and the virtual value φ_F(v) = v − (1 − F(v))/f(v) satisfies φ_F(v′) − φ_F(v) ≥ α(v′ − v) for all v′ ≥ v in the support S_F → μ ≪ Lebesgue measure, and v ↦ Γ_α^{−1}(F̄(v)) is convex on {v ≥ 0 : F̄(v) > 0}; reason: the paper's own equivalent form, used in the proof of Lemma 2 (p. App-10, after Schweizer–Szech); it avoids evaluating an a.e.-defined density pointwise and takes the support to be an interval, as the paper's proofs do (with a gap in the support, e.g. F̄ = e^{−v} on [0,1], e^{−1} on [1,2], e^{−(v−1)} beyond, the pointwise condition holds at α = 1 but Lemma 2 fails at w = 0, w′ = 2, v = 1.5)
--   - encoding: q_w Γ_α(Γ_α^{−1}(q_{w′}/q_w)(v − w)/(w′ − w)) with Γ_α^{−1}(0) := +∞, Γ_α(+∞) := 0 (p. 16) → G_α(v | (w, q_w), (w′, q_{w′})) with the q_{w′} = 0 branch: q_w for v ≤ w and 0 for v > w; reason: the paper's conventions give exactly these values; when q_w = 0 (hence q_{w′} = 0) the printed q_{w′}/q_w is 0/0 and Lean's value is 0, the only value compatible with 0 ≤ F̄ ≤ q_w
--   - encoding: a cdf F on [0, ∞) with 0 < E_F[v] < ∞ (class G, p. 11), F̄ = 1 − F → a probability measure μ on ℝ with μ((−∞, 0)) = 0, v ↦ v integrable, 0 < ∫ v dμ; F̄(p) = μ((p, ∞)); reason: same objects; F̄(p) = 1 − F(p) = P(v > p) is the strict tail
-- source:
--   Allouah, Bahamou, Besbes, Pricing with Samples, SSRN 3334650 (rev. 06/02/2021), p. 18, Lemma 2

import Mathlib
import Definitions.Def_PricingSamples_OneSampleMHR_Setting

namespace PricingSamples.OneSampleMHR

open MeasureTheory

/-- Lemma 2 (p. 18), single crossing: for `F ∈ 𝓕_α` and `0 ≤ w < w′`, `F̄` lies above the
two-point generalized Pareto interpolant `G_α(· | (w, q_w), (w′, q_{w′}))` on `[w, w′]` and below
it on `[w′, ∞)`. -/
theorem lemma_2 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) (hF : InFAlpha α μ)
    (w w' : ℝ) (hw : 0 ≤ w) (hww' : w < w') :
    (∀ v, w ≤ v → v ≤ w' → Galpha α w (ccdf μ w) w' (ccdf μ w') v ≤ ccdf μ v) ∧
      (∀ v, w' ≤ v → ccdf μ v ≤ Galpha α w (ccdf μ w) w' (ccdf μ w') v) := by sorry

end PricingSamples.OneSampleMHR
