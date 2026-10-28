-- Prove2me | Theorems.Thm_SinglePointPricing_Det_sFamily_subset_fClass
-- name    : SinglePointPricing.Det.sFamily_subset_fClass
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:57.170196+00:00
-- url     : https://prove2.me/theorems/501315d8-af71-4f9c-9d61-6d86c4028f0b
-- title:
--   §3, p. 14 — the worst-case family is admissible: S_{α,w,q} ⊂ F_α(w,q)
-- statement:
--   Let $\alpha\in[0,1]$, $w>0$ and $q\in(0,1)$. Every law of the one-parameter family
--   $$\mathcal S_{\alpha,w,q} = \{F_\alpha(\cdot\mid r,(w,q)) : r\in[\underline r_\alpha(w,q),w)\cup[w,\overline r_\alpha(w,q)]\}$$
--   of truncated generalized Pareto laws (3.4) belongs to $\mathcal F_\alpha(w,q)$: it has finite positive mean, it is α-strongly regular, and its conversion rate at $w$ is $\overline F(w) = q$. That is,
--   $$\mathcal S_{\alpha,w,q}\subseteq\mathcal F_\alpha(w,q).$$
--
--   This makes the reduction of Theorem 1 an equality between two infima over nested classes, and it shows that $\mathcal F_\alpha(w,q)$ is nonempty.
--
--   Differences from the source:
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p); reason: the page defines the data as the fraction of values greater than or equal to w (p. 2), the revenue as ∫ p 1{v ≥ p} dF(v) = p F̄(p) (p. 9), and its worst cases (3.1) as ccdfs equal to the atom's size at the top of the support; only the closed tail makes these agree, and the two tails differ only at atoms
--   - reading: α-strong regularity: a positive density on the support [a, b] except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (p. 11, App-1) → Γ_α^{−1} ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: with h = Γ_α^{−1} ∘ F̄ the α-virtual value is (1 − α)v − (1 + (1 − α)h)/h′, which is non-decreasing exactly when h is convex; convexity on {F̄ > 0} allows exactly an atom at the top of the support (as p. 11 does) and excludes interior atoms and singular parts. The printed 'non-increasing' (p. 11) is a slip for non-decreasing (App. A; proof of Lemma C-1)
--   - encoding: r ≤ r̄_α(w, q) = w/(αΓ_α^{−1}(q)), with r̄_0 = +∞ → α Γ_α^{−1}(q) r ≤ w; reason: Γ_α^{−1}(q) > 0 for q ∈ (0, 1), so the condition is the same, and at α = 0 it is r < +∞
--   - reading: w, the historical price, with no sign stated in the theorem → hypothesis 0 < w; reason: w is a posted price and Lemma C-2 states w > 0; at w = 0 no law has F̄(0) = q < 1
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, §3, p. 14, sentence after (3.4) ('It is possible to establish that S_{α,w,q} ⊂ F_α(w, q)')

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

/-- §3, p. 14: every element of the worst-case family `S_{α,w,q}` is an `α`-strongly regular value
law with conversion rate `q` at `w`, i.e. `S_{α,w,q} ⊂ F_α(w, q)`. -/
theorem sFamily_subset_fClass (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    SFamily α w q ⊆ FClass α w q := by sorry

end SinglePointPricing.Det
