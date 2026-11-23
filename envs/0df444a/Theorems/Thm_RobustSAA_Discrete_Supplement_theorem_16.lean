-- Prove2me | Theorems.Thm_RobustSAA_Discrete_Supplement_theorem_16
-- name    : RobustSAA.Discrete.Supplement.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:47:34.619039+00:00
-- url     : https://prove2.me/theorems/3be99b64-2912-4985-8101-0f1f979f222c
-- title:
--   Theorem 16 (corrected: N ≥ d + 1) — explicit finite-sample threshold (49) for the LCX statistic
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be closed, $N\ge2$ and $N\ge d+1$, let $\xi^1,\dots,\xi^N$ be iid from $F$, and let $\bar Q=\bar Q_{R_N}(\alpha_2)$ be a data-dependent bound with $\mathbb P(\mathbb E_F[\|\xi\|_2^2]\le\bar Q)\ge1-\alpha_2$, $\alpha_2\ge0$. Let $\alpha_1\in(0,1)$ and $F_0\preceq_{LCX}F$. Then $p$ of (50) lies in $(1,2)$, and with probability at least $1-\alpha_1-\alpha_2$ both $\mathbb E_F[\|\xi\|_2^2]\le\bar Q$ and
--
--   $$C_N(F_0)\le(1+\bar Q)\Big(1+\frac p{2-p}\Big)\frac{2^{1/2+1/p}}{N^{1-1/p}}\sqrt{d+1+(d+1)\log\frac N{d+1}+\log\frac4{\alpha_1}},\qquad p=\tfrac12\Big(\sqrt{\log256+8\log N+(\log2N)^2}-\log2N\Big).\tag{49}$$
--
--   Moreover, for every deterministic $B\ge\mathbb E_F[\|\xi\|_2^2]$, the right-hand side of (49) with $\bar Q=B$ is a valid threshold at level $\alpha_1$: $\mathbb P\big(C_N(F_0)>\text{RHS}(B)\big)\le\alpha_1$.
--
--   The bound gives an explicit, closed-form threshold $Q_{C_N}(\alpha_1)$ for the LCX test (16).
--
--   Differences from the source:
--   - correction: N ≥ 2 → N ≥ 2 and N ≥ d + 1; reason: (52) uses the growth-function bound (eN/(d+1))^{d+1}, valid for N ≥ d + 1; with d = 20, N = 2 the root's argument is negative for α₁ near 1 (the printed bound is undefined; Lean's √ would give 0) and ≈ 0 for α₁ ≈ 4e^{−28.4}, while C_N(F) > 0 almost surely for a continuous F on a small ball (DISPROOF.md); excluded: N < d + 1
--   - reading: with probability at least 1 − α → the outer probability of the failure event is at most α; reason: strongest form; no measurability of the events presupposed
--   - reading: Hence Q_{C_N}(α₁) = RHS of (49) is a valid threshold at level α₁ → for every deterministic B ≥ E_F‖ξ‖₂², P(C_N(F₀) > RHS(B)) ≤ α₁; reason: with a random Q̄ the union bound gives only α₁ + α₂, which is the main clause; the level-α₁ claim holds for a sure moment bound (α₂ = 0)
--   - encoding: α₂ a significance level → α₂ ≥ 0; reason: ENNReal.ofReal would clamp a negative α₂
--   - encoding: F₀ ⪯_LCX F via (12) → via the hinge form (13); reason: equivalent by Theorem 3.A.1 of [44], as the page states
--   - encoding: E_F‖ξ‖₂² ≤ Q̄ → lower integral in [0,∞] compared with Q̄ in EReal; reason: an infinite second moment is represented, not defaulted to 0
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 16, (49)–(50), p. 34 (proof pp. 34–35)

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_LCX

namespace RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Convergence
open scoped ENNReal

theorem theorem_16 {d N : ℕ} (hN : 2 ≤ N) (hdN : d + 1 ≤ N) (Ξ : Set (Pt d))
    (hΞ : IsClosed Ξ) (F F₀ : ProbabilityMeasure ↥Ξ) (hLCX : LCXle F₀ F)
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁ ∧ α₁ < 1) (hα₂ : 0 ≤ α₂) (Qbar : (Fin N → ↥Ξ) → ℝ)
    (hQbar : dataLaw F {ω | ¬ (((secondMoment F : ℝ≥0∞) : EReal) ≤
        ((Qbar (sample ω N) : ℝ) : EReal))} ≤ ENNReal.ofReal α₂) :
    (1 < pExp N ∧ pExp N < 2) ∧
    dataLaw F {ω | ¬ (((secondMoment F : ℝ≥0∞) : EReal) ≤ ((Qbar (sample ω N) : ℝ) : EReal) ∧
        lcxStat F₀ (sample ω N) ≤ ((lcxThreshold d N α₁ (Qbar (sample ω N)) : ℝ) : EReal))} ≤
      ENNReal.ofReal (α₁ + α₂) ∧
    ∀ B : ℝ, ((secondMoment F : ℝ≥0∞) : EReal) ≤ (B : EReal) →
      dataLaw F {ω | ¬ (lcxStat F₀ (sample ω N) ≤ ((lcxThreshold d N α₁ B : ℝ) : EReal))} ≤
        ENNReal.ofReal α₁ := by sorry

end RobustSAA.Discrete.Supplement
