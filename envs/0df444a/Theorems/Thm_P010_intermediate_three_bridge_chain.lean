-- Prove2me | Theorems.Thm_P010_intermediate_three_bridge_chain
-- name    : P010.intermediate_three_bridge_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:26.334997+00:00
-- url     : https://prove2.me/theorems/1c1bf5d3-1fa3-4b4a-aef9-00e348523d02
-- title:
--   P010: intermediate three bridge chain
-- statement:
--   An unpaired intermediate class may be bridged through the
--   class of 3 along the edge 9--3p.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1210-L1231
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1210-L1231

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.intermediate_three_bridge_chain (n p : ℕ) (hn : 12 ≤ n)
    (hp : Nat.Prime p) (hquarter : n / 4 < p)
    (hthird : p ≤ n / 3) :
    NonCoprimeChain
      (orderedPrimeClass n 3 6 9 ++
       orderedPrimeClass n p (3 * p) (2 * p)) := by sorry
