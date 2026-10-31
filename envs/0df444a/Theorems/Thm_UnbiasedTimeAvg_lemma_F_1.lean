-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_lemma_F_1
-- name    : UnbiasedTimeAvg.lemma_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:45.709374+00:00
-- url     : https://prove2.me/theorems/867fe34e-fcb4-4d31-a4f4-fc812ab2bea0
-- title:
--   Lemma F.1 — bounds on $k\nu_{k,l}$
-- statement:
--   Let $\nu$ be a positive non-increasing sequence with (2.4), $k\ge1$ and $b'(k)\le k/2$. Then:
--
--   1. for $l\ge0$, $$k\,\nu_{k,l}\le2\big(\bar\nu(\lfloor b'(k)/2\rfloor)\big)^2;\qquad(\mathrm F.1)$$
--   2. for $l\ge2$, $$k\,\nu_{k,l}\le2^{3-l}\big(\bar\nu(k2^{l-2})-\bar\nu(k2^{l-1})\big)^2.\qquad(\mathrm F.2)$$
--
--   Combined with Lemma F.2, these give the right-hand side of (3.4).
--
--   Differences from the source:
--   - reading: ν a "positive decreasing sequence" (A1, p.4) → `0 < ν i` and `Antitone ν` (non-increasing); reason: "decreasing" is ambiguous between strict and non-strict; the non-strict reading is the weaker hypothesis and covers the strict one, and every step of the proof uses only ν(i) ≥ ν(j) for i ≤ j
--   - encoding: burn-in b′(k) ≤ k/2 (§3.2, p.8) → a natural `b'` with `2 * b' ≤ k`; reason: the statement is for one fixed k; b(k) does not enter it
--   - encoding: 2^{3−l} → `(2 : ℝ) ^ ((3 : ℤ) - l)`; reason: an integer power, since 3 − l < 0 for l > 3
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Lemma F.1, (F.1)–(F.2), p.27; proof p.28

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_A1Sequence
import Definitions.Def_UnbiasedTimeAvg_nuBar
import Definitions.Def_UnbiasedTimeAvg_nuKL

namespace UnbiasedTimeAvg

/-- **Lemma F.1 (bounds on `ν_{k,l}`).** Kahalé, arXiv:2209.09581v1, Lemma F.1, p.27: "For
`l ≥ 0`, `kν_{k,l} ≤ 2(ν̄(⌊b′(k)/2⌋))²` (F.1), and, for `l ≥ 2`,
`kν_{k,l} ≤ 2^{3−l}(ν̄(k2^{l−2}) − ν̄(k2^{l−1}))²` (F.2)."

`ν` is the sequence of Assumption A1, `k ≥ 1` and `b′(k) ≤ k/2`.

**Formalization Note.** `2^{3−l}` is the integer power `(2 : ℝ) ^ ((3 : ℤ) - l)`; `l - 2`, `l - 1`
are natural-number subtractions under `2 ≤ l`, so they do not truncate. `⌊b′/2⌋` is `b' / 2`. -/
theorem lemma_F_1 {ν : ℕ → ℝ} (hν : A1Sequence ν) (b' k : ℕ) (hk : 1 ≤ k) (hb' : 2 * b' ≤ k) :
    (∀ l : ℕ, (k : ℝ) * nuKL ν b' k l ≤ 2 * (nuBar ν (b' / 2)) ^ 2) ∧
    (∀ l : ℕ, 2 ≤ l → (k : ℝ) * nuKL ν b' k l
      ≤ (2 : ℝ) ^ ((3 : ℤ) - l) * (nuBar ν (k * 2 ^ (l - 2)) - nuBar ν (k * 2 ^ (l - 1))) ^ 2) := by sorry

end UnbiasedTimeAvg
