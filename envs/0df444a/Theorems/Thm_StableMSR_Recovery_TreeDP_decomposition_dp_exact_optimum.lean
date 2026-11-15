-- Prove2me | Theorems.Thm_StableMSR_Recovery_TreeDP_decomposition_dp_exact_optimum
-- name    : StableMSR.Recovery.TreeDP.decomposition_dp_exact_optimum
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T09:10:11.137721+00:00
-- url     : https://prove2.me/theorems/c235355c-a873-47eb-8aaa-cd861894915e
-- title:
--   Exact optimization on a finite tree decomposition with global table and candidate bounds
-- statement:
--   Let a finite tree decomposition have $N$ bags and local validity, nonnegative integer count and real weight contributions. Suppose each bag has at most $W$ variables and at most $B$ assignment choices. There exists a coherent binary plan with $2N-1$ nodes, preserving these bounds, whose global evaluations are exactly the original locally representable valid assignments, with their original aggregate count and weight.
--
--   For every count cap $K$, its root table has at most $B(K+1)$ entries, and
--
--   $$\text{total retained entries}\le (2N-1)B(K+1),$$
--   $$\text{total raw candidates}\le (2N-1)B^3(K+1)^2.$$
--
--   For each feasible requested count $j\le K$, the root table contains an entry realized by a global assignment minimizing the sum of the original weights among all valid locally representable assignments with total count $j$. The bounds concern finite tables and enumerated tuples; no interpreter instruction count is asserted. This connects the canonical tree-decomposition interface to the exact local optimization recurrence used in clustering recovery.
-- source:
--   Prove2Me mission Exact Sum-of-Radii Clustering under Any Constant Stability; finite tree-decomposition dynamic programming correctness and enumeration bounds.

import Definitions.Def_StableMSR_BinaryTreeDP_Recurrence
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Mathlib.Data.Finset.Card
open StableMSR.Recovery.TreeDP
open scoped BigOperators

theorem StableMSR.Recovery.TreeDP.decomposition_dp_exact_optimum {V X T : Type} [DecidableEq V]
    [Fintype T] [DecidableEq T] (G : SimpleGraph V) (tree : SimpleGraph T)
    (data : T → BagData V X)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree (fun t => (data t).bag))
    (root : T) (width choices : ℕ)
    (hlocal : ∀ t, (data t).Local)
    (hbound : ∀ t, (data t).bag.card ≤ width ∧ (data t).choices.card ≤ choices) :
    ∃ p : Plan V X,
      p.Coherent ∧ p.Local ∧ p.nodes + 1 = 2 * Fintype.card T ∧
      p.AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices) ∧
      (∀ cap, (solve cap p).card ≤ choices * (cap + 1)) ∧
      (∀ cap,
        p.tableVolume cap ≤ (2 * Fintype.card T - 1) * (choices * (cap+1)) ∧
        p.rawCandidateVolume cap ≤ (2 * Fintype.card T - 1) * (choices ^ 3 * (cap+1) ^ 2)) ∧
      (∀ (whole : V → X) (j : ℕ) (w : ℝ),
        GlobalEvaluates p whole j w ↔
          (∀ t, (data t).valid whole) ∧
          (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
          (∑ t, (data t).count whole) = j ∧ (∑ t, (data t).weight whole) = w) ∧
      ∀ cap j, j ≤ cap →
        (∃ whole : V → X, (∀ t, (data t).valid whole) ∧
          (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
          (∑ t, (data t).count whole) = j) →
        ∃ e ∈ solve cap p, ∃ whole : V → X,
          e.2.1 = j ∧ (∀ t, (data t).valid whole) ∧
          (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
          (∑ t, (data t).count whole) = j ∧
          (∑ t, (data t).weight whole) = e.2.2 ∧
          ∀ other : V → X, (∀ t, (data t).valid other) →
            (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag other a) →
            (∑ t, (data t).count other) = j → e.2.2 ≤ ∑ t, (data t).weight other := by sorry
