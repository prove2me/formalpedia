-- Prove2me | Theorems.Thm_SinglePointPricing_Det_lemma_1
-- name    : SinglePointPricing.Det.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:01.301748+00:00
-- url     : https://prove2.me/theorems/c7e82801-0757-411e-ac4b-9658420b7848
-- title:
--   Lemma 1 (Single Crossing Property), p. 17 — an α-strongly regular ccdf crosses the GPD interpolant through (s, q_s), (s′, q_{s′}) once
-- statement:
--   Fix $\alpha\in[0,1]$, an α-strongly regular value law $F$ on $[0,\infty)$, and $0\le s\le s'$ with $q_{s'} = \overline F(s')>0$; write $q_s = \overline F(s)$. Then
--   $$\overline F(v)\ \ge\ q_s\,\Gamma_\alpha\Big(\Gamma_\alpha^{-1}\big(\tfrac{q_{s'}}{q_s}\big)\tfrac{v-s}{s'-s}\Big)\quad\text{for } v\in[s,s'],\qquad \overline F(v)\ \le\ q_s\,\Gamma_\alpha\Big(\Gamma_\alpha^{-1}\big(\tfrac{q_{s'}}{q_s}\big)\tfrac{v-s}{s'-s}\Big)\quad\text{for } v\in(s',+\infty).$$
--
--   The generalized Pareto interpolant through the two points $(s,q_s)$ and $(s',q_{s'})$ thus bounds the ccdf from below between them and from above beyond; this is the comparison principle behind the reduction of nature's problem to the family $\mathcal S_{\alpha,w,q}$.
--
--   Differences from the source:
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p); reason: the page defines the data as the fraction of values greater than or equal to w (p. 2), the revenue as ∫ p 1{v ≥ p} dF(v) = p F̄(p) (p. 9), and its worst cases (3.1) as ccdfs equal to the atom's size at the top of the support; only the closed tail makes these agree, and the two tails differ only at atoms
--   - reading: α-strong regularity: a positive density on the support [a, b] except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (p. 11, App-1) → Γ_α^{−1} ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: with h = Γ_α^{−1} ∘ F̄ the α-virtual value is (1 − α)v − (1 + (1 − α)h)/h′, which is non-decreasing exactly when h is convex; convexity on {F̄ > 0} allows exactly an atom at the top of the support (as p. 11 does) and excludes interior atoms and singular parts. The printed 'non-increasing' (p. 11) is a slip for non-decreasing (App. A; proof of Lemma C-1)
--   - generalization: 'F in F_α' (α-strongly regular laws, the class of the paper) → any α-strongly regular probability measure on [0, ∞), with no condition on the mean; reason: the Lean statement covers every α-strongly regular law and so specializes to the paper's F_α, whose laws in addition have 0 < E[v] < ∞
--   - encoding: (v − s)/(s′ − s) when s = s′ (undefined on the page; footnote 1 calls this case an abuse) → Lean's x/0 = 0; reason: at s = s′ the two bounds become F̄(s) ≥ F̄(s) and F̄(v) ≤ F̄(s) for v > s, which are true; the case s < s′ is unchanged
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Lemma 1, p. 17

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting

namespace SinglePointPricing.Det

open MeasureTheory

/-- Lemma 1 (Single Crossing Property), p. 17: for an `α`-strongly regular value law `F` on `[0, ∞)` and
`0 ≤ s ≤ s′` with `q_{s′} = F̄(s′) > 0` (and `q_s = F̄(s)`), the ccdf lies above the generalized
Pareto interpolant `q_s Γ_α(Γ_α^{−1}(q_{s′}/q_s)(v − s)/(s′ − s))` on `[s, s′]` and below it on
`(s′, +∞)`. -/
theorem lemma_1 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hSR : IsAlphaSR α μ) (s s' : ℝ) (hs : 0 ≤ s) (hss' : s ≤ s')
    (hq : 0 < sf μ s') :
    (∀ v ∈ Set.Icc s s',
      sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s)) ≤ sf μ v) ∧
    (∀ v ∈ Set.Ioi s',
      sf μ v ≤ sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s))) := by sorry

end SinglePointPricing.Det
