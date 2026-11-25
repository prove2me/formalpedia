-- Prove2me | Theorems.Thm_SimpleGraph_choose_le_card_cliqueFinset_add_mul_choose
-- name    : SimpleGraph.choose_le_card_cliqueFinset_add_mul_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:42:17.843128+00:00
-- url     : https://prove2.me/theorems/ee8ee78f-9509-5ed9-88c9-2a2b5518809e
-- title:
--   Simple Graph: choose le card clique Finset add mul choose
-- statement:
--   **Supersaturation by averaging.** If every `m`-set of vertices of `G` contains a `t`-clique of
--   `G` or of `Gᶜ`, then `G` and `Gᶜ` have at least `C(n, t) / C(m, t)` `t`-cliques together.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L109-L124
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L109-L124

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}

theorem SimpleGraph.choose_le_card_cliqueFinset_add_mul_choose [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t m : ℕ} (htm : t ≤ m) (hm : m ≤ Fintype.card V)
    (h : ∀ M : Finset V, #M = m →
      (∃ K ⊆ M, G.IsNClique t K) ∨ ∃ K ⊆ M, Gᶜ.IsNClique t K) :
    (Fintype.card V).choose t ≤ (#(G.cliqueFinset t) + #(Gᶜ.cliqueFinset t)) * m.choose t := by sorry
