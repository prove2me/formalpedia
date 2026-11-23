-- Prove2me | Theorems.Thm_SinglePointPricing_Det_Supplement_proposition_F_2
-- name    : SinglePointPricing.Det.Supplement.proposition_F_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:33:21.696669+00:00
-- url     : https://prove2.me/theorems/74e0088b-c0ef-4e48-abc1-163124a9a1f7
-- title:
--   Proposition F-2 — grid approximation with discretization and truncation losses
-- statement:
--   Let $\alpha\in[0,1]$, $w>0$, and $0<q_l\le q_h<1$. Fix a nonnegative price law $\Psi\in\mathcal P$, an integer $N>1$, and a strictly increasing grid $A=(a_0,\ldots,a_N)$ with $a_0=\underline r_\alpha(w,q_l)$ and $a_N\ge w$. There is one price law $\Psi_A\in\mathcal P_A$, supported on this grid, such that
--   $$
--   \inf_{F\in\mathcal F_\alpha(w,[q_l,q_h])}R(\Psi_A,F)\ge
--   \inf_{F\in\mathcal F_\alpha(w,[q_l,q_h])}R(\Psi,F)
--   -\frac{\Delta(A)}{\underline r_\alpha(w,q_l)}
--   -\frac{\mathbf1\{a_N<\overline r_\alpha(w,q_h)\}}
--    {q_h\bigl(1+(q_h^{-1}-1)a_N/w\bigr)}.
--   $$
--   Here $\Delta(A)=\max_{0\le i<N}(a_{i+1}-a_i)$. The law $\Psi_A$ may depend on $\Psi$ and $A$, and is chosen before the value law $F$. Both error terms are retained, including the normalization by $w$ in the truncation term. This supplies the discretization support for Theorem 4 on the full interval class.
--
--   Differences from the source:
--   - encoding: the indicator of a_N < r̄_α(w,q_h), with r̄_0=+∞ → the indicator of α Γ_α⁻¹(q_h) a_N < w; reason: q_h ∈ (0,1) makes Γ_α⁻¹(q_h) positive; multiplication is equivalent for α>0, while at α=0 the indicator is one for every finite a_N
--   - encoding: Δ(A) is the supremum of consecutive grid gaps → sSup of the finite nonempty set {a_{i+1}-a_i : i < N}; reason: N > 1 makes the index nonempty, and finite sets are bounded; this is the actual maximum, without truncated natural subtraction
--   - encoding: laws F, pricing cdfs Ψ, and infima of performance ratios → the published probability-measure interfaces and real suprema and infima; reason: same base mission conventions; nonnegative value laws have finite positive mean, making their oracle positive and all mechanism ratios integrable and in [0,1]
--   - encoding: w is the historical price and α and the conversion rates satisfy the standing model assumptions → w > 0, α ∈ [0,1], and all conversion endpoints lie in (0,1); reason: pp. 8–11 and the Appendix F context exclude undefined or infeasible data; these are the standing assumptions, not additional regularity
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p) of the published Setting; reason: p. 2 speaks of values greater than or equal to w and Rev uses 1{v ≥ p}; with the strict tail the terminal atoms of the worst-case family would sell with probability 0 at their own price
--   - reading: α-strong regularity: a positive density on the support, except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (printed non-increasing on p. 11) → the published IsAlphaSR: Γ_α⁻¹ ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: non-increasing is a slip for non-decreasing (the same page defines regular laws by a non-decreasing virtual value); the convexity form is that condition and allows the atom at the top of the support
--   - reading: increasing sequence of reals → strictly increasing on the finite index range; reason: a grid lists distinct prices; the programs require a_N < w = a_{N+1}, and a_N < w is derived from this
--   - encoding: a finite grid and its weights; P_A is printed on indices 1..N with a_i inside the sum over j → sequences ℕ → ℝ read only on the finite index range; P_A is the Dirac mixture Σ_j p_j δ_{a_j} on that range; reason: values outside the range are never read; a_i inside the sum is an index slip for a_j, and shifting the first index does not change the set of laws
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Proposition F-2, p. App-40

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Supplement_Grid
import Definitions.Def_SinglePointPricing_Det_Supplement_Interval

namespace SinglePointPricing.Det.Supplement

open MeasureTheory

/-- Proposition F-2: one discretized law, independent of nature's value law,
with both error terms and the scale factor `a N / w` in the truncation term. -/
theorem proposition_F_2 (α w ql qh : ℝ)
    (hα : α ∈ Set.Icc 0 1) (hw : 0 < w)
    (hql : ql ∈ Set.Ioo 0 1) (hqh : qh ∈ Set.Ioo 0 1) (hlh : ql ≤ qh)
    (Ψ : Measure ℝ) (hΨ : IsMech Ψ) (N : ℕ) (hN : 1 < N)
    (a : ℕ → ℝ) (ha : IncreasingGrid a (N + 1))
    (ha0 : a 0 = rLow α w ql) (haN : w ≤ a N) :
    ∃ ΨA : Measure ℝ, ΨA ∈ GridClass a (N + 1) ∧
      sInf (ratio Ψ '' FClassI α w ql qh) - gridGap a N / rLow α w ql -
        (if α * GammaAInv α qh * a N < w then 1 else 0) /
          (qh * (1 + (qh⁻¹ - 1) * a N / w)) ≤
        sInf (ratio ΨA '' FClassI α w ql qh) := by sorry

end SinglePointPricing.Det.Supplement
