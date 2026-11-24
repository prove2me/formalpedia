-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem32_7
-- name    : ShockWear.Inherit.Supplement.theorem32_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:49:46.200277+00:00
-- url     : https://prove2.me/theorems/de59819d-971c-4200-852c-7f4e282a3726
-- title:
--   Theorem 3.2 (3.7) — Increasing failure ratios give a logarithmically convex positive-time density
-- statement:
--   Let $\lambda>0$ and $1\ge\bar P_0\ge\bar P_1\ge\cdots\ge0$. Set $p_{k+1}=\bar P_k-\bar P_{k+1}$ and let $h$ be the positive-time density formula (2.3). If the ratios $p_{k+1}/p_k$ increase for $k\ge1$, then
--
--   $$
--   h(x+s)h(t)\le h(x+t)h(s)\qquad(x>0,\ 0<s\le t).
--   $$
--
--   Thus the positive-time density is logarithmically convex. The possible atom $1-\bar P_0$ at time zero is retained and does not belong to this density.
--
--   **Formalization Note** The source states increasing ratios on their defined domain; we state their nonnegative cross-product form, for every pair $1\le j\le k$. This is the standard zero-compatible log-convex reading, rather than dividing by zero. The density is the published (2.3) series.
--
--   Differences from the source:
--   - encoding: shock survival probabilities and Poisson rate → explicit λ>0, nonnegative antitone P with P₀≤1; reason: these are the probability assumptions in (1.1)–(2.2); P₀<1 retains the mass at the origin
--   - encoding: successive ratios on their nonzero-denominator domain → all ordered cross-product inequalities on the nonnegative sequence; reason: this is the zero-compatible log-convex or PF₂ ratio convention; no division-by-zero value is used, and no inference from adjacent ratios across gaps is assumed
--   - generalization: H is a proper life distribution, implicitly Pₖ→0 → the analytic class assertion also allows defective shock survivals; reason: bounded nonnegative coefficients still give convergent Poisson series and the same shape conclusion; every proper source law is included
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 634, Theorem 3.2 (3.7); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem32_7 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hinc : ∀ j k, 1 ≤ j → j ≤ k →
      failProb P (j + 1) * failProb P k ≤ failProb P (k + 1) * failProb P j) :
    IsLogConvexDens (shockDens lam P) := by sorry

end ShockWear.Inherit.Supplement
