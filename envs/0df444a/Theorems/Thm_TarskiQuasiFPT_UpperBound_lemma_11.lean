-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_11
-- name    : TarskiQuasiFPT.UpperBound.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:00.988688+00:00
-- url     : https://prove2.me/theorems/6fa126ff-62b7-4623-9ca6-6adfb9307b6f
-- title:
--   Lemma 11 — exclusion from $\mathrm{Fix}(Q)$ by a point postfixed (prefixed) in the coordinates $I$
-- statement:
--   Let $Q$ be a safe query-answer set, $z\in[n]^k$ and $I\subseteq[k]$.
--
--   1. If $h(z)_i\ge z_i$ for every $i\in I$ and every monotone $h\Rightarrow Q$, then $x\notin\mathrm{Fix}(Q)$ for every $x$ with
--   $$x_j\ge z_j\ \text{for all } j\in[k]\setminus I\qquad\text{and}\qquad x_i<z_i\ \text{for some } i\in I.$$
--   2. If $h(z)_i\le z_i$ for every $i\in I$ and every monotone $h\Rightarrow Q$, then $x\notin\mathrm{Fix}(Q)$ for every $x$ with $x_j\le z_j$ for all $j\in[k]\setminus I$ and $x_i>z_i$ for some $i\in I$.
--
--   Lemma 12 applies it with $I=J$ or $I=H$.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 11, PDF p. 11 (printed p. 10)

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 11 (PDF p. 11): let `Q` be a safe query-answer set, `z ∈ [n]^k` and `I ⊆ [k]`.
(i) If `h(z)_i ≥ z_i` for every `i ∈ I` and every monotone `h ⇒ Q`, then `x ∉ Fix(Q)` for every
`x` with `x_j ≥ z_j` for all `j ∉ I` and `x_i < z_i` for some `i ∈ I`.
(ii) Dually with `≤`, `≤` and `>`. -/
theorem lemma_11 {n k : ℕ} [NeZero n] (Q : QASet n k) (hQ : IsSafeQA Q) (z : Point n k)
    (I : Finset (Fin k)) :
    ((∀ h : Point n k → Point n k × Label, Monotone h → Consistent h Q →
        ∀ i ∈ I, z i ≤ (h z).1 i) →
      ∀ x : Point n k, (∀ j, j ∉ I → z j ≤ x j) → (∃ i ∈ I, x i < z i) → x ∉ Fix Q) ∧
    ((∀ h : Point n k → Point n k × Label, Monotone h → Consistent h Q →
        ∀ i ∈ I, (h z).1 i ≤ z i) →
      ∀ x : Point n k, (∀ j, j ∉ I → x j ≤ z j) → (∃ i ∈ I, z i < x i) → x ∉ Fix Q) := by sorry

end TarskiQuasiFPT.UpperBound
