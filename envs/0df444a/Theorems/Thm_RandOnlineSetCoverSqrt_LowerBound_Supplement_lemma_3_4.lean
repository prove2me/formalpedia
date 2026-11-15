-- Prove2me | Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_Supplement_lemma_3_4
-- name    : RandOnlineSetCoverSqrt.LowerBound.Supplement.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:12:55.664228+00:00
-- url     : https://prove2.me/theorems/76506d76-13f6-4829-843a-53aef85595b5
-- title:
--   Lemma 3.4 — union-expanding family of size N + q
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $m,k,r$ be integers with $1\le k\le r\le m$ and
--   $$\frac{\binom mk}{\binom rk}\ge 32e,$$
--   and put $q:=\min\{m,\binom rk+1\}$. Then there are an integer $N\ge1$ and an $(m,k,q,r)$-union-expanding candidate family $C$ of exactly $N+q$ distinct members (each a $k$-subset of $[m]$, and the union of any $q$ distinct members has more than $r$ elements) such that
--   $$\frac{N}{q^2}\ \ge\ c\cdot\frac1m\cdot\frac{\binom mk}{\binom rk}.$$
--
--   The family feeds the multi-party set-disjointness reduction of Lemma 6.1 in the proof of Theorem 1.5. Union expansion is the published predicate of the base mission (which includes $q\ge2$; here $q\ge2$ follows from the hypotheses).
--
--   Differences from the source:
--   - encoding: subsets of [m] and integer parameters → finite subsets of Fin m and natural-number parameters; reason: zero-based relabeling; nonnegativity holds under 1 ≤ k ≤ r ≤ m
--   - encoding: N/q² = Ω((1/m)·binom(m,k)/binom(r,k)) → one constant c > 0, chosen before m, k, r, with c·(1/m)·binom(m,k)/binom(r,k) ≤ N/q² in real arithmetic; reason: the meaning of the uniform Ω; real casts avoid truncated division
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, Lemma 3.4, printed p. 9 / PDF p. 10

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement

/-- Lemma 3.4, printed p. 9 / PDF p. 10. The `Ω` constant `c` is universal: it is chosen
before `m, k, r`. Here `q = min m (binom(r,k) + 1)`. -/
theorem lemma_3_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ m k r : ℕ, 1 ≤ k → k ≤ r → r ≤ m →
      32 * Real.exp 1 ≤ (Nat.choose m k : ℝ) / (Nat.choose r k : ℝ) →
      ∃ N : ℕ, 1 ≤ N ∧ ∃ C : Family m,
        C.card = N + min m (Nat.choose r k + 1) ∧
        UnionExpanding k (min m (Nat.choose r k + 1)) r C ∧
        c * ((1 / (m : ℝ)) * ((Nat.choose m k : ℝ) / (Nat.choose r k : ℝ))) ≤
          (N : ℝ) / ((min m (Nat.choose r k + 1) : ℕ) : ℝ) ^ 2 := by sorry

end RandOnlineSetCoverSqrt.LowerBound.Supplement
