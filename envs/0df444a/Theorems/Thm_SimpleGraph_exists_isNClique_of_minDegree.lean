-- Prove2me | Theorems.Thm_SimpleGraph_exists_isNClique_of_minDegree
-- name    : SimpleGraph.exists_isNClique_of_minDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:23.131972+00:00
-- url     : https://prove2.me/theorems/961ce707-2c09-4ca6-9991-87e89c1b6728
-- title:
--   Simple Graph: exists is NClique of min Degree
-- statement:
--   **Minimum degree forces cliques.** In a graph on `n` vertices with minimum degree `δ`, if
--   `j * (n - δ) < n` then there is a `(j + 1)`-clique. For `j = k` this says that
--   `δ > (1 - 1/k) n` forces a `(k + 1)`-clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L258-L275
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L258-L275

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)

theorem SimpleGraph.exists_isNClique_of_minDegree [Fintype V] [DecidableRel G.Adj] {j : ℕ}
    (hj : j * (Fintype.card V - G.minDegree) < Fintype.card V) :
    ∃ s, G.IsNClique (j + 1) s := by sorry
