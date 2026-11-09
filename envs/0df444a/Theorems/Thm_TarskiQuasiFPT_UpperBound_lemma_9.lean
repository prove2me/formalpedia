-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_9
-- name    : TarskiQuasiFPT.UpperBound.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:13.152045+00:00
-- url     : https://prove2.me/theorems/6cc9b063-fb2e-4299-a0c2-4fd9e4e9c75d
-- title:
--   Lemma 9 — coordinate separation reduces to one SafeTarski$^*(n,k-1)$ call plus one query
-- statement:
--   Let $Q$ be a safe query-answer set such that $(\mathrm{Fix}^-(Q),\mathrm{Fix}^+(Q))$ is coordinate-separable along coordinate $k$, i.e.
--   $$\max_{x\in\mathrm{Fix}^-(Q)}x_k\ \le\ \min_{y\in\mathrm{Fix}^+(Q)}y_k .$$
--   Then there is a deterministic algorithm that, given $Q$ and oracle access to any safe $g\Rightarrow Q$, makes at most
--   $$\mathrm{SafeTarski}^*(n,k-1)+1$$
--   additional queries and outputs a solution of $g$.
--
--   This is the last phase of the algorithm of Theorem 5.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
--   - encoding: labels in {±1} with −1 < +1; positive solution (x,0) ⪯ f(x), negative solution f(x) ⪯ (x,0) → Label = {neg < pos}; IsPosSolution f x := x ⪯ (f x).1 ∧ (f x).2 = pos, IsNegSolution f x := (f x).1 ⪯ x ∧ (f x).2 = neg; reason: 0 lies strictly between −1 and +1, so 0 ≤ label iff label = +1 and label ≤ 0 iff label = −1
--   - encoding: coordinate k (the last coordinate) → c : Fin k with c + 1 = k; reason: c is exactly the last coordinate in 0-based indexing; c + 1 = k also encodes k ≥ 1
--   - encoding: max_{x∈A} x_k ≤ min_{y∈B} y_k → ∀ x ∈ A, ∀ y ∈ B, x_c ≤ y_c; reason: equal on nonempty sets; with an empty set both read as true (max ∅ = −∞, min ∅ = +∞)
--   - encoding: an algorithm (given the stated data) that makes at most B (additional) queries → ∃ T : QAlgorithms.DecisionTree (a deterministic adaptive decision tree whose queries return the whole answer f(x)), chosen after the stated data and before the oracle, with T.queries g ≤ B for every admissible g; reason: a deterministic adaptive query algorithm is a decision tree; free computation between queries is the tree's branching; answers already in Q need no query
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 9, PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryComplexity
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

open QAlgorithms

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 9 (PDF p. 9): let `Q` be a safe query-answer set such that `(Fix⁻(Q), Fix⁺(Q))` is
coordinate-separable along the last coordinate `c` (the paper's coordinate `k`). There is a
deterministic algorithm (a decision tree, which may depend on `Q`) that, against any safe
`g ⇒ Q`, makes at most `SafeTarski*(n, k − 1) + 1` queries and outputs a solution of `g`. -/
theorem lemma_9 {n k : ℕ} [NeZero n] (c : Fin k) (hc : (c : ℕ) + 1 = k)
    (Q : QASet n k) (hQ : IsSafeQA Q)
    (hsep : CoordSeparable c (FixMinus Q) (FixPlus Q)) :
    ∃ T : DecisionTree (Point n k) (Point n k × Label) (Point n k),
      ∀ g : Point n k → Point n k × Label, IsSafe g → Consistent g Q →
        IsSolution g (T.eval g) ∧ T.queries g ≤ safeTarskiStarQC n (k - 1) + 1 := by sorry

end TarskiQuasiFPT.UpperBound
