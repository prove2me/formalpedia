-- Prove2me | Theorems.Thm_SinglePointPricing_Det_Supplement_proposition_F_1
-- name    : SinglePointPricing.Det.Supplement.proposition_F_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:32:36.151556+00:00
-- url     : https://prove2.me/theorems/309c7245-08aa-4fda-a727-5de64bc9a487
-- title:
--   Proposition F-1 — fundamental reduction under interval information
-- statement:
--   Let $\alpha\in[0,1]$, $w>0$, and $0<q_l\le q_h<1$. For any subclass $\mathcal P'\subseteq\mathcal P$ of nonnegative pricing mechanisms,
--   $$
--   \mathcal R(\mathcal P',\mathcal F_\alpha(w,[q_l,q_h]))=
--   \mathcal R(\mathcal P',\mathcal S_{\alpha,w,q_l,q_h}).
--   $$
--   The interval class on the left contains all α-strongly regular nonnegative value laws of finite positive mean whose conversion at $w$ lies in $[q_l,q_h]$. The family on the right uses the published truncated Pareto law with parameter $r\in[\underline r_\alpha(w,q_l),w)$ and data $q_l$, together with its high-parameter branch $w\le r\le\overline r_\alpha(w,q_h)$ and data $q_h$. The high branch is empty if its upper endpoint is below $w$.
--
--   This is the interval-information reduction supporting Theorem 4. Equality of the information endpoints is allowed, and no nonemptiness condition is imposed on the mechanism subclass.
--
--   Differences from the source:
--   - encoding: r ≤ r̄_α(w,q_h), with r̄_0=+∞ → α Γ_α⁻¹(q_h) r ≤ w; reason: the multiplied inequality represents every finite admissible r including all r ≥ w at α=0, and yields an empty high branch when r̄_α < w
--   - encoding: laws F, pricing cdfs Ψ, and infima of performance ratios → the published probability-measure interfaces and real suprema and infima; reason: same base mission conventions; nonnegative value laws have finite positive mean, making their oracle positive and all mechanism ratios integrable and in [0,1]
--   - encoding: w is the historical price and α and the conversion rates satisfy the standing model assumptions → w > 0, α ∈ [0,1], and all conversion endpoints lie in (0,1); reason: pp. 8–11 and the Appendix F context exclude undefined or infeasible data; these are the standing assumptions, not additional regularity
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p) of the published Setting; reason: p. 2 speaks of values greater than or equal to w and Rev uses 1{v ≥ p}; with the strict tail the terminal atoms of the worst-case family would sell with probability 0 at their own price
--   - reading: α-strong regularity: a positive density on the support, except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (printed non-increasing on p. 11) → the published IsAlphaSR: Γ_α⁻¹ ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: non-increasing is a slip for non-decreasing (the same page defines regular laws by a non-decreasing virtual value); the convexity form is that condition and allows the atom at the top of the support
--   - encoding: the family elements, given by their ccdfs F̄_α(·|r,(w,q)) → probability measures on [0, ∞) whose closed tail equals that ccdf on v ≥ 0; reason: each such left-continuous ccdf determines exactly one law
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Proposition F-1, p. App-40; (F-1), p. App-39

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Supplement_IntervalFamily

namespace SinglePointPricing.Det.Supplement

open MeasureTheory

/-- Proposition F-1, including the singleton-information case and arbitrary
(possibly empty) subclasses of pricing mechanisms. -/
theorem proposition_F_1 (α w ql qh : ℝ)
    (hα : α ∈ Set.Icc 0 1) (hw : 0 < w)
    (hql : ql ∈ Set.Ioo 0 1) (hqh : qh ∈ Set.Ioo 0 1) (hlh : ql ≤ qh)
    (P' : Set (Measure ℝ)) (hP : P' ⊆ {Ψ | IsMech Ψ}) :
    maximin P' (FClassI α w ql qh) = maximin P' (SFamilyI α w ql qh) := by sorry

end SinglePointPricing.Det.Supplement
