-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_proposition_C_1
-- name    : UnbiasedTimeAvg.proposition_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:42.860161+00:00
-- url     : https://prove2.me/theorems/4d2921b1-27b2-415a-9644-67e5b76cf71f
-- title:
--   Proposition C.1 — $\sum_{i=2h}^{h'}\nu(i)\le\bar\nu(h)^2$
-- statement:
--   Let $\nu$ be a positive non-increasing sequence with $\sum_i\sqrt{\nu(i)/(i+1)}<\infty$. For nonnegative integers $h,h'$ with $2h\le h'$,
--   $$\sum_{i=2h}^{h'}\nu(i)\le\big(\bar\nu(h)\big)^2.$$
--
--   In particular $\sum_i\nu(i)<\infty$; the bound converts sums of $\nu$ into the tail quantity $\bar\nu$ that appears in all constants.
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Proposition C.1, p.23

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_A1Sequence
import Definitions.Def_UnbiasedTimeAvg_nuBar

namespace UnbiasedTimeAvg

/-- **Proposition C.1 (tail of the sequence `ν`).** Kahalé, arXiv:2209.09581v1, Proposition C.1,
p.23: "For non-negative integers `h, h′` with `2h ≤ h′`, we have `Σ_{i=2h}^{h′} ν(i) ≤ (ν̄(h))²`."

**Formalization Note.** `ν` is the sequence of Assumption A1: positive, non-increasing, with
(2.4) (`A1Sequence ν`); no probability is involved. -/
theorem proposition_C_1 {ν : ℕ → ℝ} (hν : A1Sequence ν) (h h' : ℕ) (hh : 2 * h ≤ h') :
    ∑ i ∈ Finset.Icc (2 * h) h', ν i ≤ (nuBar ν h) ^ 2 := by sorry

end UnbiasedTimeAvg
