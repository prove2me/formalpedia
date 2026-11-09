-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_7
-- name    : TarskiQuasiFPT.UpperBound.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:55.529994+00:00
-- url     : https://prove2.me/theorems/6117771e-b170-4455-8773-a8acb33f2358
-- title:
--   Lemma 7 — $\mathrm{Fix}$, $\mathrm{Fix}^-$ and $\mathrm{Fix}^+$ shrink as $Q$ grows
-- statement:
--   If $Q\subseteq Q'$ are safe query-answer sets, then
--   $$\mathrm{Fix}(Q')\subseteq\mathrm{Fix}(Q),\qquad \mathrm{Fix}^-(Q')\subseteq\mathrm{Fix}^-(Q),\qquad \mathrm{Fix}^+(Q')\subseteq\mathrm{Fix}^+(Q).$$
--
--   So the set $R(Q)$ of bad point-pairs only shrinks as an algorithm queries, which is the potential argument of Theorem 5.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 7, PDF p. 8 (printed p. 7)

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 7 (PDF p. 8): if `Q ⊆ Q'` are safe query-answer sets then
`Fix(Q') ⊆ Fix(Q)`, `Fix⁻(Q') ⊆ Fix⁻(Q)` and `Fix⁺(Q') ⊆ Fix⁺(Q)`. -/
theorem lemma_7 {n k : ℕ} [NeZero n] (Q Q' : QASet n k) (hQ : IsSafeQA Q) (hQ' : IsSafeQA Q')
    (hsub : QASubset Q Q') :
    Fix Q' ⊆ Fix Q ∧ FixMinus Q' ⊆ FixMinus Q ∧ FixPlus Q' ⊆ FixPlus Q := by sorry

end TarskiQuasiFPT.UpperBound
