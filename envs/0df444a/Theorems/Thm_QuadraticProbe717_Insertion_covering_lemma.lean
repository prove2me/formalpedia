-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_covering_lemma
-- name    : QuadraticProbe717.Insertion.covering_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:22.178216+00:00
-- url     : https://prove2.me/theorems/bac583cf-6a08-4e4b-81a4-4113fd8a7edd
-- title:
--   Lemma 6.4 — covering by translated square prefixes
-- statement:
--   There is an absolute size threshold $n_0$ such that, for every odd prime $n\ge n_0$, every $0<\varepsilon\le1/2$ with $\varepsilon>1/\sqrt{\log n}$, and every integer $\varepsilon n\le k\le n/2$, the following holds. If $\Lambda\subseteq[n]$ has exactly $(1-\varepsilon)n$ occupied slots, then
--   $$\#\{j\in[n]:\{0^2,1^2,\ldots,(k-1)^2\}+j\subseteq\Lambda\}<\left\lceil2(n/k)\ln(\varepsilon^{-1})\right\rceil.$$
--   The bound is strict and holds for every occupied set of that size, with no random-table or covariance premise.
--
--   Differences from the source:
--   - reading: sufficiently large odd prime → an absolute n₀ before every prime, ε, k and occupied-set quantifier; reason: uniform sufficiently-large threshold in the source regime
--   - encoding: integer k in [εn,n/2] and the ceiling Lk,n → real lower comparison εn≤k, integer 2k≤n, and natural ceiling; reason: no load rounding and exactly the source integer thresholds
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Lemma 6.4, p. 13 (PDF p. 13)

import Definitions.Def_QuadraticProbe717_Insertion_arithmetic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem covering_lemma :
    ∃ n₀ : ℕ, ∀ (n : ℕ) [NeZero n], n₀ ≤ n → n.Prime → Odd n →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → 1 / Real.sqrt (Real.log n) < ε →
      ∀ k : ℕ, ε * n ≤ k → 2 * k ≤ n →
      ∀ A : Finset (ZMod n), (A.card : ℝ) = (1 - ε) * n →
        (badShifts n k A).card < coveringThreshold n k ε := by sorry

end QuadraticProbe717.Insertion
