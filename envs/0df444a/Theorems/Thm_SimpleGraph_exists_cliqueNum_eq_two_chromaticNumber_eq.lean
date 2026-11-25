-- Prove2me | Theorems.Thm_SimpleGraph_exists_cliqueNum_eq_two_chromaticNumber_eq
-- name    : SimpleGraph.exists_cliqueNum_eq_two_chromaticNumber_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:00:51.122043+00:00
-- url     : https://prove2.me/theorems/012b9057-d8f7-460e-91d7-de9ae4df4d51
-- title:
--   Simple Graph: exists clique Num eq two chromatic Number eq
-- statement:
--   For every `k ≥ 2`, a finite graph has clique number two and chromatic number `k`.
--
--   Source: https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L176-L202
-- source:
--   https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Erdos627/Mycielski.lean#L176-L202

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.SplitIfs
public import Definitions.Def_Erdos627_Mycielski
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
variable {V : Type*}
variable {G : SimpleGraph V} {α : Type*} {k : ℕ}
variable {W : Type*}

theorem SimpleGraph.exists_cliqueNum_eq_two_chromaticNumber_eq (k : ℕ) (hk : 2 ≤ k) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.cliqueNum = 2 ∧ G.chromaticNumber = (k : ℕ∞) := by sorry
