-- Prove2me | Theorems.Thm_SinglePointPricing_Det_lemma_D_1
-- name    : SinglePointPricing.Det.lemma_D_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:48.959268+00:00
-- url     : https://prove2.me/theorems/fa486482-19f1-4309-872a-2ba44bf8bdfc
-- title:
--   Lemma D-1, p. App-12 (corrected: right end p = 1 excluded for R_{1,α}) — order and monotonicity of the curves R_{1,α}, R_{2,α}, R_{3,α}
-- statement:
--   Let $\alpha\in[0,1]$ and $q\in(0,1)$, and write $\underline r = \underline r_\alpha(1,q)$.
--
--   1. If $q\in[\underline q_\alpha,\Gamma_\alpha(\tilde v_\alpha))$, there is $p_{13,\alpha,q}\in[\underline r,1]$ with $R_{1,\alpha}(\cdot,q)\ge R_{3,\alpha}(\cdot,q)$ on $[\underline r,p_{13,\alpha,q}]$ and $R_{1,\alpha}(\cdot,q)\le R_{3,\alpha}(\cdot,q)$ on $[p_{13,\alpha,q},1)$. If $q\in[\Gamma_\alpha(\tilde v_\alpha),1]$, then $R_{1,\alpha}(p,q)\ge R_{3,\alpha}(p,q)$ for all $p\in[\underline r,1]$.
--   2. There is $p_{12,\alpha,q}$ with $R_{1,\alpha}(\cdot,q)\ge R_{2,\alpha}(\cdot,q)$ on $[\underline r,p_{12,\alpha,q}]$ and $R_{1,\alpha}(\cdot,q)\le R_{2,\alpha}(\cdot,q)$ on $[p_{12,\alpha,q},1]$.
--   3. If $q\ge\underline q_\alpha$, then $R_{3,\alpha}(\cdot,q)$ is non-decreasing on $[\underline r,1]$.
--   4. For $\alpha\in\{0,1\}$, $R_{1,\alpha}(\cdot,q)$ is non-increasing on $[\underline r,1)$ and $R_{2,\alpha}(\cdot,q)$ is non-decreasing on $[\underline r,1]$.
--
--   These single-crossing and monotonicity facts reduce the supremum of Proposition D-1 to a comparison at the crossing points $p_{13,\alpha,q}$ and $p_{12,\alpha,q}$.
--
--   Differences from the source:
--   - correction: part 1: R_{1,α}(·, q) ≤ R_{3,α}(·, q) in [p_{13,α,q}, 1] → on [p_{13,α,q}, 1); reason: false at p = 1: α = 0, q = 3/10 ∈ [q̲_0, Γ_0(ṽ_0)) = [0, 1/2): R_{1,0}(1, q) = 1 > 7/10 = R_{3,0}(1, q), so no p_{13} works at p = 1 (µ_{0,q}(1) = 1 puts F_0(·|µ(1), (1, q)) in the r ≥ w branch of (3.2))
--   - correction: part 4: R_{1,α}(·, q) is non increasing in [r̲_α(1, q), 1] → non-increasing on [r̲_α(1, q), 1); reason: false at p = 1: α = 0, q = 3/10: R_{1,0}(1, q) = 1 while R_{1,0}(p, q) → 3/10 as p ↑ 1 (R_{1,0}(0.999, q) ≈ 0.316)
--   - reading: the intervals [q̲_α, Γ_α(ṽ_α)) and [Γ_α(ṽ_α), 1] for q → hypothesis q ∈ (0, 1) in addition; reason: the paper assumes q ∈ (0, 1) throughout (p. 11: 'the interval I does not contain 0 or 1')
--   - encoding: opt(F_α(·|r, (w, q))) → sup_{v ≥ 0} v F̄_α(v|r, (w, q)), computed from the ccdf (3.2); reason: (2.1) applied to the law whose ccdf on [0, ∞) is F̄_α(·|r, (w, q))
--   - reading: R_{3,0}(p, q) with r̄_0(1, q) = +∞ → (Γ_0^{−1}(q)/ṽ_0) · p Γ_0(Γ_0^{−1}(q) p); reason: at α = 0 the law F_0(·|+∞, (1, q)) is the untruncated tail Γ_0(Γ_0^{−1}(q)v), whose opt is the limit ṽ_0/Γ_0^{−1}(q) (p. App-17); for α ∈ (0, 1] R_{3,α} is encoded exactly as printed
--   - reading: Rev(p|δ_1)/Rev(1|δ_1) with F̄ = 1 − F for a right-continuous cdf F (p. 9), under which Rev(1|δ_1) = 1·P(v > 1) = 0 → R_{2,α}(p, q) = p F̄_{δ_1}(p)/(1·F̄_{δ_1}(1)) with the closed tail F̄(p) = P(v ≥ p), so R_{2,α}(p, q) = p on [0, 1]; reason: the page's revenue is ∫ p 1{v ≥ p} dF(v) = p F̄(p) (p. 9), which is the closed tail; only it makes R_{2,α} defined and equal to p, as the proof of Theorem 2 uses (R_{2,α}(p_{12,α,q}, q) = p_{12,α,q}, App-13)
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Lemma D-1, p. App-12

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

/-- Lemma D-1, p. App-12, corrected at `p = 1` in part 1 (first sentence) and part 4 (`R_{1,α}`):
1. if `q ∈ [q̲_α, Γ_α(ṽ_α))` there is `p₁₃ ∈ [r̲_α(1,q), 1]` with `R_{1,α} ≥ R_{3,α}` on
   `[r̲_α(1,q), p₁₃]` and `R_{1,α} ≤ R_{3,α}` on `[p₁₃, 1)`; if `q ∈ [Γ_α(ṽ_α), 1]`,
   `R_{1,α} ≥ R_{3,α}` on `[r̲_α(1,q), 1]`;
2. there is `p₁₂` with `R_{1,α} ≥ R_{2,α}` on `[r̲_α(1,q), p₁₂]` and `R_{1,α} ≤ R_{2,α}` on `[p₁₂, 1]`;
3. if `q ≥ q̲_α`, `R_{3,α}` is non-decreasing on `[r̲_α(1,q), 1]`;
4. for `α ∈ {0, 1}`, `R_{1,α}` is non-increasing on `[r̲_α(1,q), 1)` and `R_{2,α}` is non-decreasing
   on `[r̲_α(1,q), 1]`. -/
theorem lemma_D_1 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    ((q ∈ Set.Ico (qLow α) (GammaA α (vTilde α)) →
        ∃ p13 ∈ Set.Icc (rLow α 1 q) 1,
          (∀ p ∈ Set.Icc (rLow α 1 q) p13, R3 α q p ≤ R1 α q p) ∧
          (∀ p ∈ Set.Ico p13 1, R1 α q p ≤ R3 α q p)) ∧
      (q ∈ Set.Icc (GammaA α (vTilde α)) 1 →
        ∀ p ∈ Set.Icc (rLow α 1 q) 1, R3 α q p ≤ R1 α q p)) ∧
    (∃ p12 : ℝ,
      (∀ p ∈ Set.Icc (rLow α 1 q) p12, R2 p ≤ R1 α q p) ∧
      (∀ p ∈ Set.Icc p12 1, R1 α q p ≤ R2 p)) ∧
    (qLow α ≤ q → MonotoneOn (R3 α q) (Set.Icc (rLow α 1 q) 1)) ∧
    ((α = 0 ∨ α = 1) →
      AntitoneOn (R1 α q) (Set.Ico (rLow α 1 q) 1) ∧
      MonotoneOn R2 (Set.Icc (rLow α 1 q) 1)) := by sorry

end SinglePointPricing.Det
