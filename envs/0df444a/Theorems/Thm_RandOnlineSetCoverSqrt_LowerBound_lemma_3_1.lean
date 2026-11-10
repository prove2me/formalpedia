-- Prove2me | Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_1
-- name    : RandOnlineSetCoverSqrt.LowerBound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T19:34:22.690037+00:00
-- url     : https://prove2.me/theorems/1ac7501e-1dc6-4145-b1da-7c69f2d1d50a
-- title:
--   Lemma 3.1 — forcing iff and exact batch-length bound
-- statement:
--   Let $D$ be a nonempty family of nonempty subsets of $[m]$, and let $r\ge1$ be an integer. There is a finite ordered batch $B$ of elements of $U_m$ such that
--
--   $$|B|\le\sum_{j=0}^r\binom mj,$$
--
--   and for every purchased label set $X\subseteq[m]$ with $|X|\le r$,
--
--   $$X\text{ covers every element of }B\quad\Longleftrightarrow\quad\exists W\in D,\ W\subseteq X.$$
--
--   Candidates need not have equal size or be disjoint. No upper bound $r\le m$ is imposed; binomial coefficients with index larger than $m$ are zero. The existence of a nonempty candidate implies $m\ge1$, so no separate positivity assumption on $m$ is needed.
--
--   This batch interface transfers candidate containment into coverage of actual requests.
--
--   Differences from the source:
--   - encoding: subsets of [m] and nonnegative integer parameters → finite subsets of Fin m and natural-number parameters; reason: zero-based relabeling and nonnegativity in the type change no source instance
--   - encoding: a sequence of elements u_A and its coverage → a list of nonempty incidence subtypes with the published coverage predicate; reason: A is the complete identity of u_A on the canonical known system; the iff and full length bound are unchanged
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Lemma 3.1, printed p. 8 / PDF p. 9

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates

namespace RandOnlineSetCoverSqrt.LowerBound

/-- Lemma 3.1, printed p. 8 / PDF p. 9. No upper restriction r ≤ m is imposed. -/
theorem lemma_3_1 {m : ℕ} (D : Family m) (hD : D.Nonempty)
    (hne : ∀ W ∈ D, W.Nonempty) (r : ℕ) (hr : 1 ≤ r) :
    ∃ B : List (Element m), Forcing r D B ∧ B.length ≤ batchBound m r := by sorry

end RandOnlineSetCoverSqrt.LowerBound
