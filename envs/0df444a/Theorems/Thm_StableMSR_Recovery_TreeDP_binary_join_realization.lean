-- Prove2me | Theorems.Thm_StableMSR_Recovery_TreeDP_binary_join_realization
-- name    : StableMSR.Recovery.TreeDP.binary_join_realization
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T02:25:38.423112+00:00
-- url     : https://prove2.me/theorems/5031c4d0-7b66-46fe-98bc-d4307773f223
-- title:
--   Binary DP realization with exact accounting and linear node overhead
-- statement:
--   A parent bag and any finite list of coherent local child plans satisfying the rooted separator conditions admit an explicit coherent local binary plan. Its root bag and assignment choices agree with the parent, its scope is exactly the union of the original scopes, and it checks exactly the original constraints. For every assignment its total count and objective are the original parent contribution plus the child totals, with no duplication. The new plan has exactly one parent node plus one binary join per child plus all child nodes. Uniform bag-width and assignment-choice bounds are preserved. This proves the fanout-to-binary conversion used by the local clustering DP; obtaining a size-bounded decomposition and executing the entire DP are separate obligations.
-- source:
--   Prove2Me Exact Sum-of-Radii Clustering under Any Constant Stability, local tree-decomposition DP: explicit binary expansion by neutral duplicate bags.

import Definitions.Def_StableMSR_BinaryTreeDP_Plan
import Mathlib.Data.Finset.Card
open StableMSR.Recovery.TreeDP

theorem StableMSR.Recovery.TreeDP.binary_join_realization {V X : Type*} [DecidableEq V]
    (d : BagData V X) (children : List (Plan V X)) (width choices : ℕ)
    (hdlocal : d.Local)
    (hcoherent : ∀ p ∈ children, p.Coherent)
    (hlocal : ∀ p ∈ children, p.Local)
    (hparent : ∀ p ∈ children, p.scope ∩ d.bag ⊆ p.root.bag)
    (hpair : children.Pairwise (fun p q => p.scope ∩ q.scope ⊆ d.bag))
    (hdbound : d.bag.card ≤ width ∧ d.choices.card ≤ choices)
    (hbound : ∀ p ∈ children,
      p.AllData (fun a => a.bag.card ≤ width ∧ a.choices.card ≤ choices)) :
    ∃ p : Plan V X,
      p.Coherent ∧ p.Local ∧ p.root.bag = d.bag ∧ p.root.choices = d.choices ∧
      (∀ v, v ∈ p.scope ↔ v ∈ d.bag ∨ ∃ child ∈ children, v ∈ child.scope) ∧
      (∀ a : V → X,
        (p.AllValid a ↔ d.valid a ∧ ∀ child ∈ children, child.AllValid a) ∧
        p.totalCount a = d.count a + (children.map (fun child => child.totalCount a)).sum ∧
        p.totalWeight a = d.weight a + (children.map (fun child => child.totalWeight a)).sum) ∧
      p.nodes = 1 + children.length + (children.map Plan.nodes).sum ∧
      p.AllData (fun a => a.bag.card ≤ width ∧ a.choices.card ≤ choices) := by sorry
