-- Prove2me | Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_3
-- name    : RandOnlineSetCoverSqrt.LowerBound.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T19:34:14.248289+00:00
-- url     : https://prove2.me/theorems/17104e09-f62a-44c4-908e-9b6273b12e32
-- title:
--   Lemma 3.3 — binomial criterion for union expansion
-- statement:
--   Let $m,k,q,r,M$ be nonnegative integers with $1\le k\le r\le m$, $q\ge2$, and $M\le\binom mk$. If
--
--   $$\binom Mq\binom mr\left(\frac{\binom rk}{\binom mk}\right)^q<1,$$
--
--   then there is an $(m,k,q,r)$-union-expanding candidate family $C$ with exactly $M$ distinct members. Each member is a $k$-subset, and the union of every $q$ distinct members has size strictly greater than $r$. This includes $M=0$ and $M<q$, where the expansion condition is vacuous exactly as in the source. The denominator is positive because $k\le m$.
--
--   This is the general existence criterion used for the eventual square-root parameters.
--
--   Differences from the source:
--   - encoding: subsets of [m] and nonnegative integer parameters → finite subsets of Fin m and natural-number parameters; reason: zero-based relabeling and nonnegativity in the type change no source instance
--   - encoding: ratio of binomial counts → real casts before division; reason: the criterion uses real rather than truncated natural division
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Lemma 3.3, printed p. 8 / PDF p. 9

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates

namespace RandOnlineSetCoverSqrt.LowerBound

/-- Lemma 3.3, printed p. 8 / PDF p. 9, of STOC 2027 submission #1160. -/
theorem lemma_3_3 (m k q r M : ℕ)
    (hk : 1 ≤ k) (hkr : k ≤ r) (hrm : r ≤ m) (hq : 2 ≤ q)
    (hM : M ≤ Nat.choose m k)
    (hfirst : (Nat.choose M q : ℝ) * (Nat.choose m r : ℝ) *
      ((Nat.choose r k : ℝ) / (Nat.choose m k : ℝ)) ^ q < 1) :
    ∃ C : Family m, C.card = M ∧ UnionExpanding k q r C := by sorry

end RandOnlineSetCoverSqrt.LowerBound
