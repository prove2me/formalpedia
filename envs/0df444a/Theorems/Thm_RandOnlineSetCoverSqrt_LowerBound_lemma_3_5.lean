-- Prove2me | Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_5
-- name    : RandOnlineSetCoverSqrt.LowerBound.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T19:34:27.656719+00:00
-- url     : https://prove2.me/theorems/5245fd0e-63c6-4ee7-ae66-4dd84e59752f
-- title:
--   Lemma 3.5 — expanding families at the exact square-root parameters
-- statement:
--   There is an integer threshold $m_0$ such that for every integer $m\ge m_0$, define
--
--   $$k=\lfloor\sqrt m\rfloor,\quad q=\lceil\sqrt m\rceil,\quad r=\lfloor m/32\rfloor,\quad M=2^{4q}.$$
--
--   There exists an $(m,k,q,r)$-union-expanding candidate family of exactly $M$ members. In particular, $1\le k\le r\le m$ and $q\ge2$, every member has size $k$, and every subfamily of $q$ distinct members has union size strictly greater than $r$.
--
--   This supplies the candidate families for every sufficiently large integer $m$, including nonsquares; the threshold is independent of any online algorithm.
--
--   Differences from the source:
--   - encoding: subsets of [m] and nonnegative integer parameters → finite subsets of Fin m and natural-number parameters; reason: zero-based relabeling and nonnegativity in the type change no source instance
--   - encoding: floors and ceilings of nonnegative real numbers → natural floors and ceilings; r=m/32 in natural division; reason: these operations have exactly the displayed integer values
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Lemma 3.5, printed p. 9 / PDF p. 10, proof continues printed p. 10 / PDF p. 11

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates

namespace RandOnlineSetCoverSqrt.LowerBound

/-- Lemma 3.5, printed p. 9 / PDF p. 10; proof continues PDF p. 11. -/
theorem lemma_3_5 :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ C : Family m,
      C.card = familySize m ∧ UnionExpanding (kParam m) (qParam m) (rParam m) C := by sorry

end RandOnlineSetCoverSqrt.LowerBound
