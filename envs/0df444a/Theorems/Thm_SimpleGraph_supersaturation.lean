-- Prove2me | Theorems.Thm_SimpleGraph_supersaturation
-- name    : SimpleGraph.supersaturation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:37:09.57759+00:00
-- url     : https://prove2.me/theorems/5a3dbdc6-0be1-447f-ba46-b3b0eb08ba33
-- title:
--   Simple Graph: supersaturation
-- statement:
--   **Supersaturation via the Erdős–Szekeres recursion.** Let `k, l ≥ 1` with `k + l ≥ 3`, and let
--   `S` be a finite vertex set with `x = |S| + 1 - 2 ^ (k + l - 3) > 0`. Then `G` has at least
--   `2 ^ (-E(k, l)) x ^ k / k!` `k`-cliques inside `S`, or `Gᶜ` has at least
--   `2 ^ (-E(l, k)) x ^ l / l!` `l`-cliques inside `S`, where `E(k, l) = k (l - 2) + C(k + 1, 2) - 1`
--   (see `supersaturationBound`).
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L411-L415
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L411-L415

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

theorem SimpleGraph.supersaturation {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (h3 : 3 ≤ k + l) (S : Finset V)
    (hx : 0 < (#S : ℝ) + 1 - 2 ^ (k + l - 3)) :
    supersaturationBound k l ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ G.cliqueCountIn S k ∨
      supersaturationBound l k ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ Gᶜ.cliqueCountIn S l := by sorry
