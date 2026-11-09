-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_3
-- name    : TarskiQuasiFPT.UpperBound.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:32.045317+00:00
-- url     : https://prove2.me/theorems/b48c9c5f-1064-40fe-832d-552658350058
-- title:
--   Lemma 3 — $J_s(Q)\preceq x^*\preceq M_s(Q)$ for the slice fixed point $x^*$ of every consistent safe function
-- statement:
--   Let $Q$ be a safe query-answer set and $h$ a safe function with $h\Rightarrow Q$. For every slice $s$ of $[n]^k$, the fixed point $x^*$ of $h$ on $s$ satisfies
--   $$J_s(Q)\preceq x^*\preceq M_s(Q),$$
--   and in particular $J_s(Q)\preceq M_s(Q)$.
--
--   This is why $\mathrm{Fix}(Q)$ contains the fixed point of every safe function consistent with $Q$.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
--   - encoding: the unique fixed point x* of h on slice s → every x with x ∈ L_s that is a fixed point of h on s; reason: h is safe, so there is exactly one such x; quantifying over it states the same
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 3, PDF p. 7 (printed p. 6)

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 3 (PDF p. 7): for a safe query-answer set `Q`, a safe `h` consistent with `Q` and any
slice `s`, the fixed point of `h` on `s` lies between `J_s(Q)` and `M_s(Q)`; in particular
`J_s(Q) ⪯ M_s(Q)`. -/
theorem lemma_3 {n k : ℕ} [NeZero n] (Q : QASet n k) (hQ : IsSafeQA Q)
    (h : Point n k → Point n k × Label) (hh : IsSafe h) (hhQ : Consistent h Q)
    (s : Slice n k) :
    (∀ x : Point n k, InSlice s x → IsSliceFixed h s x → Js Q s ≤ x ∧ x ≤ Ms Q s) ∧
    Js Q s ≤ Ms Q s := by sorry

end TarskiQuasiFPT.UpperBound
