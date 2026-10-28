-- Prove2me | Theorems.Thm_SinglePointPricing_Det_eq_4_1
-- name    : SinglePointPricing.Det.eq_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:10.993491+00:00
-- url     : https://prove2.me/theorems/896e239f-69d1-4b99-bc05-c77c50970a39
-- title:
--   Display (4.1), p. 21 — R(P_d, F_α(w,q)) as a sup over p ∈ [0,w] of the minimum of three worst-case ratios
-- statement:
--   Let $\alpha\in[0,1]$, $w>0$ and $q\in(0,1)$. The maximin ratio of the deterministic prices is
--   $$\mathcal R(\mathcal P_d,\mathcal F_\alpha(w,q)) = \sup_{p\in[0,w]}\min\Big\{\inf_{r\in[\underline r_\alpha(w,q),p)}\frac{p\,\overline F_\alpha(p\mid r,(w,q))}{r},\ \frac pw,\ \inf_{r\in[w,\overline r_\alpha(w,q)]}\frac{p\,\overline F_\alpha(p\mid r,(w,q))}{\mathrm{opt}(F_\alpha(\cdot\mid r,(w,q)))}\Big\},$$
--   the three terms being the worst cases with oracle price below $p$, between $p$ and $w$, and at or above $w$.
--
--   This is the paper's first reduction of the deterministic problem, from which Proposition D-1 and the closed forms of Theorem 2 follow.
--
--   Differences from the source:
--   - reading: w, the historical price, with no sign stated in the theorem → hypothesis 0 < w; reason: w is a posted price and Lemma C-2 states w > 0; at w = 0 no law has F̄(0) = q < 1
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p); reason: the page defines the data as the fraction of values greater than or equal to w (p. 2), the revenue as ∫ p 1{v ≥ p} dF(v) = p F̄(p) (p. 9), and its worst cases (3.1) as ccdfs equal to the atom's size at the top of the support; only the closed tail makes these agree, and the two tails differ only at atoms
--   - reading: α-strong regularity: a positive density on the support [a, b] except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (p. 11, App-1) → Γ_α^{−1} ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: with h = Γ_α^{−1} ∘ F̄ the α-virtual value is (1 − α)v − (1 + (1 − α)h)/h′, which is non-decreasing exactly when h is convex; convexity on {F̄ > 0} allows exactly an atom at the top of the support (as p. 11 does) and excludes interior atoms and singular parts. The printed 'non-increasing' (p. 11) is a slip for non-decreasing (App. A; proof of Lemma C-1)
--   - encoding: sup and inf in R(Ψ, F), opt(F) and R(P′, 𝓕) → sSup and sInf on ℝ; reason: every set involved is nonempty and bounded (ratios lie in [0, 1], revenues are bounded by the mean), so the real sSup and sInf are the paper's sup and inf; no junk value arises
--   - encoding: min{min_{r∈[r̲_α,p)} …, p/w, min_{r∈[w,r̄_α]} …} → sInf of the union of the three value sets; reason: the minima over half-open sets are infima (p. 21, (b): min_{r∈[p,w)} p/r = p/w is not attained), an empty group (p ≤ r̲_α, or r̄_α < w) imposes no constraint, and the infimum of a union is the minimum of the infima; the union always contains p/w
--   - encoding: opt(F_α(·|r, (w, q))) → sup_{v ≥ 0} v F̄_α(v|r, (w, q)), computed from the ccdf (3.2); reason: (2.1) applied to the law whose ccdf on [0, ∞) is F̄_α(·|r, (w, q))
--   - encoding: r ≤ r̄_α(w, q) = w/(αΓ_α^{−1}(q)), with r̄_0 = +∞ → α Γ_α^{−1}(q) r ≤ w; reason: Γ_α^{−1}(q) > 0 for q ∈ (0, 1), so the condition is the same, and at α = 0 it is r < +∞
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, §4.1, p. 21, display (4.1), line (b)

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

/-- Display (4.1), line (b), p. 21: the deterministic maximin ratio as a supremum over prices
`p ∈ [0, w]` of the smallest of three worst-case ratios,
`inf_{r ∈ [r̲_α(w,q), p)} p F̄_α(p|r,(w,q))/r`, `p/w`, and
`inf_{r ∈ [w, r̄_α(w,q)]} p F̄_α(p|r,(w,q))/opt(F_α(·|r,(w,q)))`; the minimum of the three is the
infimum of the union of the three value sets (an empty group contributes nothing). -/
theorem eq_4_1 (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ =>
        sInf (((fun r => p * Fbar α w q r p / r) '' Set.Ico (rLow α w q) p) ∪ {p / w} ∪
          ((fun r => p * Fbar α w q r p / optFun (Fbar α w q r)) ''
            {r | w ≤ r ∧ α * GammaAInv α q * r ≤ w}))) '' Set.Icc 0 w) := by sorry

end SinglePointPricing.Det
