-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_5
-- name    : TarskiQuasiFPT.UpperBound.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:37.010194+00:00
-- url     : https://prove2.me/theorems/2c423250-e2e5-4728-a815-6778af75ce20
-- title:
--   Lemma 5 — $J(Q)\in\mathrm{Fix}(Q)$ and $M(Q)\in\mathrm{Fix}(Q)$
-- statement:
--   For every safe query-answer set $Q$,
--   $$J(Q)\in\mathrm{Fix}(Q)\qquad\text{and}\qquad M(Q)\in\mathrm{Fix}(Q),$$
--   where $J(Q)$, $M(Q)$ are the greatest postfixed and least prefixed points on the whole grid.
--
--   Lemma 8 uses this to read a solution off $Q$.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 5, PDF p. 8 (printed p. 7)

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 5 (PDF p. 8): for a safe query-answer set `Q`, `J(Q) ∈ Fix(Q)` and `M(Q) ∈ Fix(Q)`. -/
theorem lemma_5 {n k : ℕ} [NeZero n] (Q : QASet n k) (hQ : IsSafeQA Q) :
    J Q ∈ Fix Q ∧ M Q ∈ Fix Q := by sorry

end TarskiQuasiFPT.UpperBound
