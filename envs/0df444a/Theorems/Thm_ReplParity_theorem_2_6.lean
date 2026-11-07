-- Prove2me | Theorems.Thm_ReplParity_theorem_2_6
-- name    : ReplParity.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:19.84851+00:00
-- url     : https://prove2.me/theorems/84985f43-c2c2-4d0a-9451-b4c665d3e35d
-- title:
--   Theorem 2.6 (chain and deletion bounds; time bound carried by the goal) — stable partition [KMM+25, Proposition 2]
-- statement:
--   Let $S$ be a finite sequence of nonzero vectors of $\mathbb F_2^n$.
--
--   1. The spans $V_1,V_2,\dots,V_\ell$ of the parts of the stable partition, in the order the passes produce them, form a chain $V_1\supseteq V_2\supseteq\dots\supseteq V_\ell$.
--   2. At most $n$ of these subspaces are distinct.
--   3. If $S_{-i}$ is obtained from $S$ by deleting its $i$-th vector, then
--   $$\max_V|n_S(V)-n_{S_{-i}}(V)|\le1\qquad\text{and}\qquad\sum_V|n_S(V)-n_{S_{-i}}(V)|\le2 .$$
--
--   The deletion bounds feed the Efron–Stein argument of Lemma 3.1.
--
--   Differences from the source:
--   - reading: "The partition can be computed in time O(|S|²n³)" → carried by ReplParity.theorem_3_6's TM2 polynomial-time clause, not stated here; reason: explicit degrees and exact real block sizes depend on a bit-cost RAM the paper does not pin down; only polynomiality is model-robust, and the goal's proof uses only that (paper.md decision 6)
--   - encoding: a chain V₁ ⊇ ⋯ ⊇ V_ℓ of at most n distinct subspaces; S_{−i} → the list of spans is pairwise ⊇ in pass order and its set of values has at most n elements; S.eraseIdx i for i < |S| (0-indexed); reason: same statement
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Theorem 2.6, p.13 (PDF p.15), citing [KMM+25, Proposition 2]

import Mathlib
import Definitions.Def_ReplParity_mult

namespace ReplParity

open Classical in
/-- **Theorem 2.6 ([KMM+25, Proposition 2]): chain and deletion stability of the stable partition.**
Shen, Zhong, *Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization*,
STOC 2027 submission (manuscript sha256 40424491…), Theorem 2.6, p.13 (PDF p.15): "The spans of the
parts of the stable partition of S form a chain V_1 ⊇ V_2 ⊇ · · · ⊇ V_ℓ of at most n distinct
subspaces. If S_{−i} is obtained from S by deleting the i-th vector, then
max_V |n_S(V) − n_{S−i}(V)| ≤ 1 and Σ_V |n_S(V) − n_{S−i}(V)| ≤ 2."

For a sequence `S` of nonzero vectors of 𝔽ⁿ₂: the spans of the parts, in pass order, decrease; at
most `n` of them are distinct; and deleting any one vector changes every multiplicity by at most `1`
and their sum of absolute changes by at most `2`. -/
theorem theorem_2_6 (n : ℕ) (S : List (Vec n)) (hS : ∀ v ∈ S, v ≠ 0) :
    ((stablePartition S).map spanOf).Pairwise (fun V W => W ≤ V) ∧
    ((stablePartition S).map spanOf).toFinset.card ≤ n ∧
    ∀ i < S.length,
      (∀ V : Subsp n, |(mult S V : ℤ) - mult (S.eraseIdx i) V| ≤ 1) ∧
      ∑ V : Subsp n, |(mult S V : ℤ) - mult (S.eraseIdx i) V| ≤ 2 := by sorry

end ReplParity
