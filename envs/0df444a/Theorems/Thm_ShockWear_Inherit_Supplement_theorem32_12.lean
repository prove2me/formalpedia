-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem32_12
-- name    : ShockWear.Inherit.Supplement.theorem32_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:52:50.160803+00:00
-- url     : https://prove2.me/theorems/0a320b09-79f0-40f9-850b-5644fb5ce1a4
-- title:
--   Theorem 3.2 (3.12) — Reversed discrete NBUE inequalities give NWUE
-- statement:
--   Let $\lambda>0$ and $1\ge\bar P_0\ge\bar P_1\ge\cdots\ge0$. Suppose
--
--   $$
--   \bar P_k\sum_{j=0}^\infty\bar P_j\le\sum_{j=k}^\infty\bar P_j\qquad(k\ge0).
--   $$
--
--   Then the Poisson shock survival $\bar H$ is new worse than used in expectation:
--
--   $$
--   \int_0^\infty\bar H(x)\,dx\le
--   \frac{\int_0^\infty\bar H(t+x)\,dx}{\bar H(t)}
--   \qquad(t\ge0,\ \bar H(t)>0).
--   $$
--
--   This transfers the comparison of total and residual discrete tails to continuous-time expected residual life, allowing infinite means.
--
--   **Formalization Note** The source states nonnegative infinite sums and integrals; we use $[0,\infty]$ for all of them, with its standard $0\cdot\infty=0$. The conditioning denominator must be positive. No finite-mean assumption is imposed.
--
--   Differences from the source:
--   - encoding: shock survival probabilities and Poisson rate → explicit λ>0, nonnegative antitone P with P₀≤1; reason: these are the probability assumptions in (1.1)–(2.2); P₀<1 retains the mass at the origin
--   - encoding: nonnegative sums and expected-life integrals, possibly infinite → ENNReal arithmetic and positive-denominator residual ratios; reason: divergence is represented by infinity and never replaced by a real default value
--   - generalization: H is a proper life distribution, implicitly Pₖ→0 → the analytic class assertion also allows defective shock survivals; reason: bounded nonnegative coefficients still give convergent Poisson series and the same shape conclusion; every proper source law is included
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 634, Theorem 3.2 (3.12); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_ReversedAgeing

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem32_12 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hnwue : ∀ k, ENNReal.ofReal (P k) * (∑' j, ENNReal.ofReal (P j)) ≤
      ∑' j, ENNReal.ofReal (P (j + k))) :
    IsNWUE (ShockWear.CumDamage.shockSurv lam P) := by sorry

end ShockWear.Inherit.Supplement
