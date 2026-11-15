-- Prove2me | Theorems.Thm_StableMSR_Recovery_TreeDP_binary_plan_from_decomposition
-- name    : StableMSR.Recovery.TreeDP.binary_plan_from_decomposition
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T09:07:31.828206+00:00
-- url     : https://prove2.me/theorems/d718f384-c945-4be9-8d2f-a1ceafa6549d
-- title:
--   An exact binary DP plan for every finite tree decomposition
-- statement:
--   Let a finite tree decomposition have $N$ bags, a specified root, and a local record at each bag. Each record specifies finitely many allowed assignments, a validity predicate, a nonnegative integer count and a real weight, all contributions depending only on the bag. Suppose every bag has at most $W$ variables and at most $B$ assignment choices. There is a coherent binary plan $P$ such that
--
--   $$|P|=2N-1.$$
--
--   Its root bag and choices are unchanged, it covers every variable, and every record still has at most $W$ variables and $B$ choices. For every global assignment, validity and local representability hold in the plan exactly when they hold at all original bags. The total count and weight equal the respective sums over the original bags. Thus binary conversion introduces neither duplicated contributions nor spurious restrictions. This statement concerns the finite representation; finding a small decomposition and compiling the DP into the recovery interpreter are separate obligations.
-- source:
--   Prove2Me mission Exact Sum-of-Radii Clustering under Any Constant Stability; finite decomposition-to-DP construction, recursive rooted-component expansion.

import Definitions.Def_StableMSR_BinaryTreeDP_Plan
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Mathlib.Data.Finset.Card
open StableMSR.Recovery.TreeDP
open scoped BigOperators

theorem StableMSR.Recovery.TreeDP.binary_plan_from_decomposition {V X T : Type} [DecidableEq V]
    [Fintype T] [DecidableEq T] (G : SimpleGraph V) (tree : SimpleGraph T)
    (data : T → BagData V X)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree (fun t => (data t).bag))
    (root : T) (width choices : ℕ)
    (hlocal : ∀ t, (data t).Local)
    (hbound : ∀ t, (data t).bag.card ≤ width ∧ (data t).choices.card ≤ choices) :
    ∃ p : Plan V X,
      p.Coherent ∧ p.Local ∧ p.root.bag = (data root).bag ∧
      p.root.choices = (data root).choices ∧
      (∀ v, v ∈ p.scope) ∧
      (∀ whole : V → X,
        (p.AllValid whole ↔ ∀ t, (data t).valid whole) ∧
        (p.AllData (fun d => ∃ a ∈ d.choices, AgreeOn d.bag whole a) ↔
          ∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
        p.totalCount whole = ∑ t, (data t).count whole ∧
        p.totalWeight whole = ∑ t, (data t).weight whole) ∧
      p.nodes + 1 = 2 * Fintype.card T ∧
      p.AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices) := by sorry
