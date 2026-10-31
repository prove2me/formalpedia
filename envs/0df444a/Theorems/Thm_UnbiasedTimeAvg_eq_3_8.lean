-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_eq_3_8
-- name    : UnbiasedTimeAvg.eq_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:19.041005+00:00
-- url     : https://prove2.me/theorems/6841c9b3-e39e-44f4-929c-369c10a893c8
-- title:
--   (3.6)–(3.8) — $(p_l)$ is a positive probability distribution with $\sum_{l\ge2}2^lp_l=1$
-- statement:
--   Let $\nu$ be a positive non-increasing sequence with (2.4), $k\ge1$, and $(p_l)$ given by (3.6)–(3.7). Then $p_l>0$ for every $l$,
--   $$\sum_{l=2}^\infty2^lp_l=\sum_{l=2}^\infty\frac{\bar\nu(k2^{l-2})-\bar\nu(k2^{l-1})}{\bar\nu(k)}=1,\qquad(3.8)$$
--   hence $\sum_{l\ge2}p_l\le1/4$, $p_1\ge1/4$, $p_0\ge1/2$, and $(p_l)_{l\ge0}$ is a probability distribution.
--
--   This makes the parameters of Theorem 3.2 admissible in Lemma 3.2.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: sums over l ≥ 2 → sums over j ≥ 0 with l = j + 2; reason: reindexing
--   - encoding: "p_l > 0 for l ≥ 2" and "(p_l, l ≥ 0) is a probability distribution" → `∀ l, 0 < p l` and `HasSum p 1`; reason: positivity of p_0, p_1 is part of the stated p_1 ≥ 1/4, p_0 ≥ 1/2; Step 2 (p.8) requires p_l > 0 for all l
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), (3.6)–(3.8) and the sentences around them, p.9

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_A1Sequence
import Definitions.Def_UnbiasedTimeAvg_nuBar
import Definitions.Def_UnbiasedTimeAvg_levelProb

namespace UnbiasedTimeAvg

/-- **(3.6)–(3.8): the `ν̄`-dependent `(p_l)` is a positive probability distribution.** Kahalé,
arXiv:2209.09581v1, p.9: "Note that `p_l > 0` for `l ≥ 2` since `(ν̄(i), i ≥ 0)` is a strictly
decreasing sequence. Furthermore, `Σ_{l=2}^∞ 2^l p_l = Σ_{l=2}^∞ (ν̄(k2^{l−2}) − ν̄(k2^{l−1}))/ν̄(k) = 1`
(3.8). Hence `Σ_{l=2}^∞ p_l ≤ 1/4`. Consequently, `p_1 ≥ 1/4`, `p_0 ≥ 1/2`, and `(p_l, l ≥ 0)` is a
probability distribution."

For `ν` as in A1 and `k ≥ 1`, with `p_l = levelProb ν k l` given by (3.6)–(3.7).

**Formalization Note.** Sums over `l ≥ 2` are reindexed by `l = j + 2`. "Probability distribution"
is `HasSum p 1` together with `p_l > 0` for every `l`. -/
theorem eq_3_8 {ν : ℕ → ℝ} (hν : A1Sequence ν) (k : ℕ) (hk : 1 ≤ k) :
    (∀ l, 0 < levelProb ν k l) ∧
    HasSum (fun j : ℕ => (nuBar ν (k * 2 ^ j) - nuBar ν (k * 2 ^ (j + 1))) / nuBar ν k) 1 ∧
    HasSum (fun j : ℕ => (2 : ℝ) ^ (j + 2) * levelProb ν k (j + 2)) 1 ∧
    ∑' j : ℕ, levelProb ν k (j + 2) ≤ 1 / 4 ∧
    1 / 4 ≤ levelProb ν k 1 ∧ 1 / 2 ≤ levelProb ν k 0 ∧
    HasSum (levelProb ν k) 1 := by sorry

end UnbiasedTimeAvg
