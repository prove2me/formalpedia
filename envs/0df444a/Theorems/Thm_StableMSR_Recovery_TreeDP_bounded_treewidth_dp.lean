-- Prove2me | Theorems.Thm_StableMSR_Recovery_TreeDP_bounded_treewidth_dp
-- name    : StableMSR.Recovery.TreeDP.bounded_treewidth_dp
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T18:03:56.913108+00:00
-- url     : https://prove2.me/theorems/fab4ffec-85ca-411e-80e5-266cca0d64e2
-- title:
--   Bounded-treewidth finite DP with a small decomposition and linear plan size
-- statement:
--   For every finite graph $G$ on $n$ vertices of treewidth at most $w$, there exists a width-$w$ tree decomposition with at most $n+1$ bags, chosen before its local data. For every matching local allocation with at most $B$ represented choices per bag, there is a coherent local binary DP plan with at most $2n+1$ nodes preserving the original validity, representability, total count, and total objective. At every feasible count at most a cap $K$, the retained table contains a represented global optimum. The root table has at most $B(K+1)$ entries and the total table and raw candidate volumes satisfy
--
--   $$T\le(2n+1)B(K+1),\qquad R\le(2n+1)B^3(K+1)^2.$$
--
--   This result removes a supplied-decomposition hypothesis while retaining explicit locality, matching-bag, and bounded-choice hypotheses. It asserts semantic correctness and finite cardinality bounds, not an instruction-level running time or a construction of application-specific local data.
-- source:
--   Composition of the proved Prove2Me results finite_decomposition_search (d4f2a14a-b18f-44f7-966a-d1411797cf17) and decomposition_dp_exact_optimum (c235355c-a873-47eb-8aaa-cd861894915e), supporting the Exact Sum-of-Radii Clustering under Any Constant Stability mission.

import Theorems.Thm_StableMSR_Recovery_DecompositionSearch_finite_decomposition_search
import Theorems.Thm_StableMSR_Recovery_TreeDP_decomposition_dp_exact_optimum
set_option autoImplicit false
open scoped Classical BigOperators
open RobertsonSeymour1986.GM5 StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.TreeDP

theorem StableMSR.Recovery.TreeDP.bounded_treewidth_dp {V X : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (width : ℕ) (htw : TreewidthLE G width) :
    ∃ (T : Type) (ft : Fintype T) (dt : DecidableEq T)
      (tree : SimpleGraph T) (bags : T → Finset V),
      IsTreeDecomposition G tree bags ∧
      (∀ t, (bags t).card ≤ width+1) ∧
      @Fintype.card T ft ≤ Fintype.card V + 1 ∧
      ∀ (data : T → BagData V X) (choices : ℕ),
        (∀ t, (data t).bag = bags t) →
        (∀ t, (data t).Local) →
        (∀ t, (data t).choices.card ≤ choices) →
        ∃ p : Plan V X,
          p.Coherent ∧ p.Local ∧ p.nodes ≤ 2 * Fintype.card V + 1 ∧
          p.AllData (fun d => d.bag.card ≤ width+1 ∧ d.choices.card ≤ choices) ∧
          (∀ cap, (solve cap p).card ≤ choices * (cap+1)) ∧
          (∀ cap,
            p.tableVolume cap ≤ (2 * Fintype.card V + 1) * (choices * (cap+1)) ∧
            p.rawCandidateVolume cap ≤
              (2 * Fintype.card V + 1) * (choices ^ 3 * (cap+1) ^ 2)) ∧
          (∀ (whole : V → X) (j : ℕ) (w : ℝ),
            GlobalEvaluates p whole j w ↔
              (∀ t, (data t).valid whole) ∧
              (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
              (∑ t, (data t).count whole) = j ∧
              (∑ t, (data t).weight whole) = w) ∧
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
                (∑ t, (data t).count other) = j →
                  e.2.2 ≤ ∑ t, (data t).weight other := by sorry
