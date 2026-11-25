-- Prove2me | Theorems.Thm_SimpleGraph_supersaturation_diag
-- name    : SimpleGraph.supersaturation_diag
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:46:30.646528+00:00
-- url     : https://prove2.me/theorems/517467c5-0de3-4ced-a245-275d7c0cc9c6
-- title:
--   Simple Graph: supersaturation diag
-- statement:
--   **Diagonal supersaturation.** For `t ≥ 2`, `G` and `Gᶜ` together have at least
--   `2 ^ (-E(t, t)) x ^ t / t!` `t`-cliques inside `S`, where `x = |S| + 1 - 2 ^ (2t - 3) > 0`.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L419-L425
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L419-L425

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
variable [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem SimpleGraph.supersaturation_diag {t : ℕ} (ht : 2 ≤ t) (S : Finset V)
    (hx : 0 < (#S : ℝ) + 1 - 2 ^ (t + t - 3)) :
    supersaturationBound t t ((#S : ℝ) + 1 - 2 ^ (t + t - 3)) ≤
      G.cliqueCountIn S t + Gᶜ.cliqueCountIn S t := by sorry
