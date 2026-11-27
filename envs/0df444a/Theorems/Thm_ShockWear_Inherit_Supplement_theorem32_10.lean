-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem32_10
-- name    : ShockWear.Inherit.Supplement.theorem32_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:51:24.587246+00:00
-- url     : https://prove2.me/theorems/606f9338-71b6-4d8d-91f4-18bc12c353fa
-- title:
--   Theorem 3.2 (3.10) — Increasing discrete survival roots give DHRA
-- statement:
--   Let $\lambda>0$ and $1\ge\bar P_0\ge\bar P_1\ge\cdots\ge0$. If the real roots $\bar P_k^{1/k}$ increase for positive integers $k$, then the Poisson shock survival $\bar H$ has decreasing hazard rate average:
--
--   $$
--   \bar H(s)^{1/s}\le\bar H(t)^{1/t}\qquad(0<s\le t).
--   $$
--
--   This transfers the reversed root-monotonicity property without requiring zero-time survival to be one.
--
--   **Formalization Note** The source states roots and monotonicity; we use `Real.rpow` with exponents $1/(k:\mathbb R)$ and $1/t$, only for positive indices and times. Zero bases are allowed.
--
--   Differences from the source:
--   - encoding: shock survival probabilities and Poisson rate → explicit λ>0, nonnegative antitone P with P₀≤1; reason: these are the probability assumptions in (1.1)–(2.2); P₀<1 retains the mass at the origin
--   - encoding: positive-index and positive-time roots → real powers with real reciprocal exponents and explicit positive domains; reason: natural-number division and a zero exponent at k=0 are excluded
--   - generalization: H is a proper life distribution, implicitly Pₖ→0 → the analytic class assertion also allows defective shock survivals; reason: bounded nonnegative coefficients still give convergent Poisson series and the same shape conclusion; every proper source law is included
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 634, Theorem 3.2 (3.10); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_ReversedAgeing

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem32_10 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k →
      P j ^ (1 / (j : ℝ)) ≤ P k ^ (1 / (k : ℝ))) :
    IsDHRA (ShockWear.CumDamage.shockSurv lam P) := by sorry

end ShockWear.Inherit.Supplement
