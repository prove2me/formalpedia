-- Prove2me | Theorems.Thm_SignRankMargin_OREquality_lemma_9
-- name    : SignRankMargin.OREquality.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:41.781495+00:00
-- url     : https://prove2.me/theorems/2b9d48b8-9cd8-4477-bf60-da752401bdfe
-- title:
--   Lemma 9 — OR compositions of sparse rows
-- statement:
--   Let $k,D,u,v\ge1$ be integers. Let $B$ be any $u\times v$ Boolean matrix with at most $D$ ones in each row. Then
--
--   $$
--   \operatorname{signRank}(\operatorname{orComposition}(k,B))\le2(D+1)^k-1.
--   $$
--
--   In particular, for every integer $n\ge1$,
--
--   $$
--   \operatorname{signRank}(\operatorname{orEquality}(k,n))\le2^{k+1}-1.
--   $$
--
--   The matrix may be rectangular; there is no column-sparsity or regularity requirement. This is the upper-bound milestone, including its equality specialization.
--
--   Differences from the source:
--   - encoding: one-based row, column and coordinate labels; equality on n-bit strings → Fin u, Fin v and Fin k labels, with alphabet Fin (2^n); reason: finite relabelling preserves every entry and the minimum real realization rank
-- source:
--   Gabriel Hart, Kaave Hosseini, STOC 2027 submission #728 (October 2026), Lemma 9, p. 9; proof pp. 9–10

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_SignRankMargin_OREquality_Composition

namespace SignRankMargin.OREquality

/-- Lemma 9, p.9: arbitrary rectangular row-sparse matrices, and the equality specialization. -/
theorem lemma_9 (k D u v : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (B : Matrix (Fin u) (Fin v) Bool)
    (hrows : ∀ x, (∑ y, if B x y then (1 : ℕ) else 0) ≤ D) :
    signRank (orComposition k B) ≤ 2 * (D + 1) ^ k - 1 ∧
    (∀ n : ℕ, 1 ≤ n → signRank (orEquality k n) ≤ 2 ^ (k + 1) - 1) := by sorry

end SignRankMargin.OREquality
