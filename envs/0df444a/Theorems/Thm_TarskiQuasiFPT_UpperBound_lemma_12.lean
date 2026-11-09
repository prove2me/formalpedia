-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_12
-- name    : TarskiQuasiFPT.UpperBound.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:57.950995+00:00
-- url     : https://prove2.me/theorems/61192504-0c83-4285-bd81-4c09202866ac
-- title:
--   Lemma 12 — one side of an antipodal pair is eliminated with SafeTarski$^*(n,\lfloor k/2\rfloor-1)+1$ queries
-- statement:
--   Let $k\ge2$, let $Q$ be a safe query-answer set, and let $S^-\subseteq\mathrm{Fix}^-(Q)$ and $S^+\subseteq\mathrm{Fix}^+(Q)$ be nonempty sets such that $(S^-,S^+)$ is antipodal (item (ii) of Lemma 10, distinguished coordinate $k$). There is a deterministic algorithm that, given $Q$, $(S^-,S^+)$ and oracle access to any safe $g\Rightarrow Q$, makes at most
--   $$\mathrm{SafeTarski}^*\bigl(n,\lfloor k/2\rfloor-1\bigr)+1$$
--   additional queries to $g$, and the set $Q'$ obtained from $Q$ by adding these queries with their answers satisfies
--   $$S^-\cap\mathrm{Fix}^-(Q')=\emptyset\qquad\text{or}\qquad S^+\cap\mathrm{Fix}^+(Q')=\emptyset.$$
--
--   This is one round of the algorithm of Theorem 5.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
--   - encoding: coordinate k (the last coordinate) → c : Fin k with c + 1 = k; reason: c is exactly the last coordinate in 0-based indexing; c + 1 = k also encodes k ≥ 1
--   - encoding: an algorithm (given the stated data) that makes at most B (additional) queries → ∃ T : QAlgorithms.DecisionTree (a deterministic adaptive decision tree whose queries return the whole answer f(x)), chosen after the stated data and before the oracle, with T.queries g ≤ B for every admissible g; reason: a deterministic adaptive query algorithm is a decision tree; free computation between queries is the tree's branching; answers already in Q need no query
--   - encoding: Q′, the extension of Q by the algorithm's queries → extendQA Q g (queriedPoints T g): Q with (y, g y) recorded at every point y queried by T against g; reason: these are exactly the pairs the algorithm learns; since g ⇒ Q, re-queried points keep their answers
--   - encoding: ⌊k/2⌋ − 1 → k / 2 − 1 in ℕ; reason: ℕ-division is the floor, and k ≥ 2 makes the subtraction exact
--   - encoding: the algorithm's output (none is specified) → the tree's leaves carry Unit; reason: only its queries matter
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 12, PDF p. 12 (printed p. 11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryComplexity
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

open QAlgorithms

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 12 (PDF p. 12): let `k ≥ 2`, `Q` a safe query-answer set and `S⁻ ⊆ Fix⁻(Q)`,
`S⁺ ⊆ Fix⁺(Q)` nonempty with `(S⁻, S⁺)` antipodal (distinguished coordinate `c`, the last one).
There is a deterministic algorithm (a decision tree, which may depend on `Q`, `S⁻`, `S⁺`) that,
against any safe `g ⇒ Q`, makes at most `SafeTarski*(n, ⌊k/2⌋ − 1) + 1` queries, and the
extension `Q'` of `Q` by the answers of `g` at the queried points satisfies
`S⁻ ∩ Fix⁻(Q') = ∅` or `S⁺ ∩ Fix⁺(Q') = ∅`. The tree's output is irrelevant (`Unit`). -/
theorem lemma_12 {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (c : Fin k) (hc : (c : ℕ) + 1 = k)
    (Q : QASet n k) (hQ : IsSafeQA Q) (Sm Sp : Finset (Point n k))
    (hSm : Sm ⊆ FixMinus Q) (hSp : Sp ⊆ FixPlus Q)
    (hSm_ne : Sm.Nonempty) (hSp_ne : Sp.Nonempty) (hanti : IsAntipodal c Sm Sp) :
    ∃ T : DecisionTree (Point n k) (Point n k × Label) Unit,
      ∀ g : Point n k → Point n k × Label, IsSafe g → Consistent g Q →
        T.queries g ≤ safeTarskiStarQC n (k / 2 - 1) + 1 ∧
        (Sm ∩ FixMinus (extendQA Q g (queriedPoints T g)) = ∅ ∨
          Sp ∩ FixPlus (extendQA Q g (queriedPoints T g)) = ∅) := by sorry

end TarskiQuasiFPT.UpperBound
