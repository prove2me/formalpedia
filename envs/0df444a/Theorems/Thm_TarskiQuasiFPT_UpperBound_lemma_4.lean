-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_4
-- name    : TarskiQuasiFPT.UpperBound.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:36.909174+00:00
-- url     : https://prove2.me/theorems/1cddf0b2-8b27-4317-a654-b52809c6697c
-- title:
--   Lemma 4 — $J_s$ increases and $M_s$ decreases as $Q$ grows
-- statement:
--   Let $Q\subseteq Q'$ be safe query-answer sets. Then for every slice $s$ of $[n]^k$,
--   $$J_s(Q)\preceq J_s(Q')\qquad\text{and}\qquad M_s(Q')\preceq M_s(Q).$$
--
--   More queries can only tighten the bounds on slice fixed points; Lemma 7 uses this.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 4, PDF p. 7 (printed p. 6)

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 4 (PDF p. 7): if `Q ⊆ Q'` are safe query-answer sets then `J_s(Q) ⪯ J_s(Q')` and
`M_s(Q') ⪯ M_s(Q)` for every slice `s`. -/
theorem lemma_4 {n k : ℕ} [NeZero n] (Q Q' : QASet n k) (hQ : IsSafeQA Q) (hQ' : IsSafeQA Q')
    (hsub : QASubset Q Q') :
    ∀ s : Slice n k, Js Q s ≤ Js Q' s ∧ Ms Q' s ≤ Ms Q s := by sorry

end TarskiQuasiFPT.UpperBound
