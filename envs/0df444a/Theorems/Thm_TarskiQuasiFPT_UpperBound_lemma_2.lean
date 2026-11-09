-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_2
-- name    : TarskiQuasiFPT.UpperBound.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:24.628722+00:00
-- url     : https://prove2.me/theorems/9ff5d39a-5fdf-48be-930a-c8d4a4a6b90d
-- title:
--   Lemma 2 — postfixed points form a nonempty join-closed set; prefixed points a nonempty meet-closed set
-- statement:
--   Let $Q$ be a safe query-answer set and $s$ a slice of $[n]^k$. Then:
--
--   1. some point is postfixed for $Q$ on $s$;
--   2. if $a$ and $b$ are postfixed for $Q$ on $s$, so is their coordinatewise join $a\vee b$;
--   3. some point is prefixed for $Q$ on $s$;
--   4. if $a$ and $b$ are prefixed for $Q$ on $s$, so is their coordinatewise meet $a\wedge b$.
--
--   Postfixed and prefixed are taken with respect to all monotone $h\Rightarrow Q$. The lemma makes $J_s(Q)$ the greatest postfixed and $M_s(Q)$ the least prefixed point.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: NeZero n and 1 ≤ n are equivalent for natural n
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 2, PDF p. 6 (printed p. 5)

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 2 (PDF p. 6): for a safe query-answer set `Q` and any slice `s`, the postfixed points
for `Q` on `s` form a nonempty set closed under coordinatewise joins, and the prefixed points a
nonempty set closed under coordinatewise meets. -/
theorem lemma_2 {n k : ℕ} [NeZero n] (Q : QASet n k) (hQ : IsSafeQA Q) (s : Slice n k) :
    (∃ y : Point n k, IsPostfixed Q s y) ∧
    (∀ a b : Point n k, IsPostfixed Q s a → IsPostfixed Q s b → IsPostfixed Q s (a ⊔ b)) ∧
    (∃ y : Point n k, IsPrefixed Q s y) ∧
    (∀ a b : Point n k, IsPrefixed Q s a → IsPrefixed Q s b → IsPrefixed Q s (a ⊓ b)) := by sorry

end TarskiQuasiFPT.UpperBound
