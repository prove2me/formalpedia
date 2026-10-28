-- Prove2me | Theorems.Thm_SinglePointPricing_Det_theorem_1
-- name    : SinglePointPricing.Det.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:37.372165+00:00
-- url     : https://prove2.me/theorems/5a51c5d5-5f35-4678-863f-50fe614cce8b
-- title:
--   Theorem 1 (Fundamental Reduction), p. 14 — R(P′, F_α(w,q)) = R(P′, S_{α,w,q}) for every mechanism class P′ ⊆ P
-- statement:
--   Fix $\alpha\in[0,1]$, a price $w>0$ and a conversion rate $q\in(0,1)$. For every subset $\mathcal P'$ of the randomized pricing mechanisms $\mathcal P$ (laws of posted prices on $[0,\infty)$),
--   $$\mathcal R(\mathcal P',\mathcal F_\alpha(w,q)) = \mathcal R(\mathcal P',\mathcal S_{\alpha,w,q}),$$
--   where $\mathcal R(\mathcal P',\mathcal F) = \sup_{\Psi\in\mathcal P'}\inf_{F\in\mathcal F}\int p\,\overline F(p)\,d\Psi(p)/\mathrm{opt}(F)$ and $\mathcal S_{\alpha,w,q}$ is the one-parameter family (3.4) of truncated generalized Pareto laws.
--
--   Nature's infinite-dimensional problem over the non-convex class $\mathcal F_\alpha(w,q)$ thus reduces to a one-dimensional problem over $r$; Theorems 2–4 of the paper rest on it.
--
--   Differences from the source:
--   - reading: w, the historical price, with no sign stated in the theorem → hypothesis 0 < w; reason: w is a posted price and Lemma C-2 states w > 0; at w = 0 no law has F̄(0) = q < 1
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p); reason: the page defines the data as the fraction of values greater than or equal to w (p. 2), the revenue as ∫ p 1{v ≥ p} dF(v) = p F̄(p) (p. 9), and its worst cases (3.1) as ccdfs equal to the atom's size at the top of the support; only the closed tail makes these agree, and the two tails differ only at atoms
--   - reading: α-strong regularity: a positive density on the support [a, b] except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (p. 11, App-1) → Γ_α^{−1} ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: with h = Γ_α^{−1} ∘ F̄ the α-virtual value is (1 − α)v − (1 + (1 − α)h)/h′, which is non-decreasing exactly when h is convex; convexity on {F̄ > 0} allows exactly an atom at the top of the support (as p. 11 does) and excludes interior atoms and singular parts. The printed 'non-increasing' (p. 11) is a slip for non-decreasing (App. A; proof of Lemma C-1)
--   - encoding: sup and inf in R(Ψ, F), opt(F) and R(P′, 𝓕) → sSup and sInf on ℝ; reason: every set involved is nonempty and bounded (ratios lie in [0, 1], revenues are bounded by the mean), so the real sSup and sInf are the paper's sup and inf; no junk value arises
--   - encoding: r ≤ r̄_α(w, q) = w/(αΓ_α^{−1}(q)), with r̄_0 = +∞ → α Γ_α^{−1}(q) r ≤ w; reason: Γ_α^{−1}(q) > 0 for q ∈ (0, 1), so the condition is the same, and at α = 0 it is r < +∞
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Theorem 1, p. 14

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

open MeasureTheory

/-- Theorem 1 (Fundamental Reduction), p. 14: for `α ∈ [0, 1]`, `q ∈ (0, 1)` and every class
`P′ ⊆ P` of pricing mechanisms, `R(P′, F_α(w, q)) = R(P′, S_{α,w,q})`. -/
theorem theorem_1 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) (hw : 0 < w) (q : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (P' : Set (Measure ℝ)) (hP' : ∀ Ψ ∈ P', IsMech Ψ) :
    maximin P' (FClass α w q) = maximin P' (SFamily α w q) := by sorry

end SinglePointPricing.Det
