-- Prove2me | Theorems.Thm_P010_isolated_two_path_weight
-- name    : P010.isolated_two_path_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:38:03.511181+00:00
-- url     : https://prove2.me/theorems/2a37bb72-60ef-4e79-a3b2-28e64ff4699b
-- title:
--   P010: isolated two path weight
-- statement:
--   For n ≥ 4, isolated vertices and vertex 2 must occupy
--   different paths of any non-coprime cover.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L741-L761
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L741-L761

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.isolated_two_path_weight (n : ℕ) (hn : 4 ≤ n) (a : List ℕ)
    (hc : NonCoprimeChain a) (hd : a.Nodup)
    (hb : ∀ t ∈ a, 0 < t ∧ t ≤ n) :
    (a.filter (fun t => decide (t ∈ isolatedVertices n))).length +
        (a.filter (fun t => decide (t = 2))).length ≤ 1 := by sorry
