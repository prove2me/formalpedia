-- Prove2me | Theorems.Thm_P010_adjacentCount_flatten_le
-- name    : P010.adjacentCount_flatten_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:38.094226+00:00
-- url     : https://prove2.me/theorems/0b9ebcb5-b21e-4e9e-a826-f7640aaea63a
-- title:
--   P010: adjacent Count flatten le
-- statement:
--   The concatenation of k non-coprime paths contains at most k-1
--   coprime adjacencies. Empty paths are harmless.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L312-L331
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L312-L331

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.adjacentCount_flatten_le (paths : List (List ℕ))
    (hpaths : ∀ p ∈ paths, NonCoprimeChain p) :
    adjacentCount paths.flatten ≤ paths.length - 1 := by sorry
