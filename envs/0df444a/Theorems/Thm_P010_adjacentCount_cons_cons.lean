-- Prove2me | Theorems.Thm_P010_adjacentCount_cons_cons
-- name    : P010.adjacentCount_cons_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:31.15015+00:00
-- url     : https://prove2.me/theorems/cfcfb86e-cf1d-4df9-8697-aa1daeb9349a
-- title:
--   P010: adjacent Count cons cons
-- statement:
--   Expanding one adjacent pair in the counted adjacency list.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L281-L286
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L281-L286

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.adjacentCount_cons_cons (x y : ℕ) (xs : List ℕ) :
    adjacentCount (x :: y :: xs) =
      (if Nat.Coprime x y then 1 else 0) + adjacentCount (y :: xs) := by sorry
