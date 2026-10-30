-- Prove2me | Theorems.Thm_SinglePointPricing_Det_proposition_D_1
-- name    : SinglePointPricing.Det.proposition_D_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:46.572075+00:00
-- url     : https://prove2.me/theorems/7ddeeb12-4ea4-4afe-a098-fa6ab85b237f
-- title:
--   Proposition D-1, pp. App-11–12 (corrected: p ∈ [0, 1)) — three worst-case laws against deterministic prices
-- statement:
--   Let $\alpha\in[0,1]$, $w>0$ and $q\in(0,1)$, and use the curves $R_{1,\alpha},R_{2,\alpha},R_{3,\alpha}$ of the normalized price $p$ (initial price normalized to 1). Then
--   $$\mathcal R(\mathcal P_d,\mathcal F_\alpha(w,q)) = \begin{cases}\sup_{p\in[0,1)}\min\{R_{1,\alpha}(p,q),R_{2,\alpha}(p,q),R_{3,\alpha}(p,q)\} & \text{if } q\in[\underline q_\alpha,1),\\ \sup_{p\in[0,1)}\min\{R_{1,\alpha}(p,q),R_{2,\alpha}(p,q)\} & \text{if } q\in(0,\underline q_\alpha).\end{cases}$$
--   Here $R_{1,\alpha}$ is the ratio against the GPD law starting at $\mu_{\alpha,q}(p)$ and truncated at 1, $R_{2,\alpha}$ against a point mass at 1, and $R_{3,\alpha}$ against the GPD law truncated at $\overline r_\alpha(1,q)$.
--
--   A deterministic price thus faces at most three worst-case laws, two of them fixed; Lemmas D-1 and D-2 then solve the resulting one-dimensional problem in closed form.
--
--   Differences from the source:
--   - correction: sup over p ∈ [0, 1] → sup over p ∈ [0, 1); reason: the printed statement is false at p = 1, where µ_{α,q}(1) = 1: α = 0, w = 1, q = 3/10: µ_{0,q}(1) = 1, so R_{1,0}(1, q) = 1, R_{2,0}(1, q) = 1 and R_{3,0}(1, q) = 7/10, and the printed right side is at least 7/10, while R(P_d, F_0(1, 3/10)) = 9/14 (Theorem 2; directly, the price 1 against F_0(·|r, (1, q)) with r ↑ 1 earns q/r → 3/10). In the second case, α = 1, q = 1/5 < q̲_1 = e^{−1}: min{R_{1,1}(1, q), R_{2,1}(1, q)} = e q log(q^{−1}) ≈ 0.875 > 0.715 ≈ β_q(e/q) = R(P_d, F_1(1, 1/5))
--   - reading: w, the historical price, with no sign stated in the theorem → hypothesis 0 < w; reason: w is a posted price and Lemma C-2 states w > 0; at w = 0 no law has F̄(0) = q < 1
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p); reason: the page defines the data as the fraction of values greater than or equal to w (p. 2), the revenue as ∫ p 1{v ≥ p} dF(v) = p F̄(p) (p. 9), and its worst cases (3.1) as ccdfs equal to the atom's size at the top of the support; only the closed tail makes these agree, and the two tails differ only at atoms
--   - reading: α-strong regularity: a positive density on the support [a, b] except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (p. 11, App-1) → Γ_α^{−1} ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: with h = Γ_α^{−1} ∘ F̄ the α-virtual value is (1 − α)v − (1 + (1 − α)h)/h′, which is non-decreasing exactly when h is convex; convexity on {F̄ > 0} allows exactly an atom at the top of the support (as p. 11 does) and excludes interior atoms and singular parts. The printed 'non-increasing' (p. 11) is a slip for non-decreasing (App. A; proof of Lemma C-1)
--   - encoding: sup and inf in R(Ψ, F), opt(F) and R(P′, 𝓕) → sSup and sInf on ℝ; reason: every set involved is nonempty and bounded (ratios lie in [0, 1], revenues are bounded by the mean), so the real sSup and sInf are the paper's sup and inf; no junk value arises
--   - encoding: opt(F_α(·|r, (w, q))) → sup_{v ≥ 0} v F̄_α(v|r, (w, q)), computed from the ccdf (3.2); reason: (2.1) applied to the law whose ccdf on [0, ∞) is F̄_α(·|r, (w, q))
--   - reading: R_{3,0}(p, q) with r̄_0(1, q) = +∞ → (Γ_0^{−1}(q)/ṽ_0) · p Γ_0(Γ_0^{−1}(q) p); reason: at α = 0 the law F_0(·|+∞, (1, q)) is the untruncated tail Γ_0(Γ_0^{−1}(q)v), whose opt is the limit ṽ_0/Γ_0^{−1}(q) (p. App-17); for α ∈ (0, 1] R_{3,α} is encoded exactly as printed
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Proposition D-1, pp. App-11–12

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

/-- Proposition D-1 (Worst-case Distributions against Deterministic Mechanisms), pp. App-11–12,
corrected: the supremum is over normalized prices `p ∈ [0, 1)` (the printed `[0, 1]` makes the
statement false at `p = 1`, where `µ_{α,q}(1) = 1`). For `q ∈ [q̲_α, 1)` the maximin ratio is
`sup_p min{R_{1,α}(p,q), R_{2,α}(p,q), R_{3,α}(p,q)}`; for `q ∈ (0, q̲_α)` it is
`sup_p min{R_{1,α}(p,q), R_{2,α}(p,q)}`. -/
theorem proposition_D_1 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) (hw : 0 < w) (q : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (qLow α ≤ q → maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ => min (R1 α q p) (min (R2 p) (R3 α q p))) '' Set.Ico 0 1)) ∧
    (q < qLow α → maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ => min (R1 α q p) (R2 p)) '' Set.Ico 0 1)) := by sorry

end SinglePointPricing.Det
