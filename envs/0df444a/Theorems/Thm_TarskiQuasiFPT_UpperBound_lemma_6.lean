-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_6
-- name    : TarskiQuasiFPT.UpperBound.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:37.190305+00:00
-- url     : https://prove2.me/theorems/f9bce47f-8608-47d5-bfb1-b6b741dd99fb
-- title:
--   Lemma 6 — a forced strict move in one coordinate excludes the point from $\mathrm{Fix}(Q)$
-- statement:
--   Let $Q$ be a safe query-answer set, $x\in[n]^k$ and $i\in[k]$. If $h(x)_i>x_i$ for every monotone $h\Rightarrow Q$, or $h(x)_i<x_i$ for every monotone $h\Rightarrow Q$, then
--   $$x\notin\mathrm{Fix}(Q).$$
--
--   Lemma 12 uses this to eliminate candidate points.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 6, PDF p. 8 (printed p. 7)

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 6 (PDF p. 8): let `Q` be a safe query-answer set. If `h(x)_i > x_i` for every monotone
`h ⇒ Q`, or `h(x)_i < x_i` for every monotone `h ⇒ Q`, then `x ∉ Fix(Q)`. -/
theorem lemma_6 {n k : ℕ} [NeZero n] (Q : QASet n k) (hQ : IsSafeQA Q)
    (x : Point n k) (i : Fin k)
    (hforce : (∀ h : Point n k → Point n k × Label, Monotone h → Consistent h Q →
                  x i < (h x).1 i) ∨
              (∀ h : Point n k → Point n k × Label, Monotone h → Consistent h Q →
                  (h x).1 i < x i)) :
    x ∉ Fix Q := by sorry

end TarskiQuasiFPT.UpperBound
