-- Prove2me | Theorems.Thm_P010_paired_intermediate_classes_chain
-- name    : P010.paired_intermediate_classes_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:13.277677+00:00
-- url     : https://prove2.me/theorems/b0c9e0a2-e8fe-491f-8ce4-603d201aaf2e
-- title:
--   P010: paired intermediate classes chain
-- statement:
--   Two intermediate prime classes can be joined along their
--   multiple-of-three endpoints into one noncoprime path.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1183-L1206
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1183-L1206

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.paired_intermediate_classes_chain (n p q : ℕ) (hn : 12 ≤ n)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpquarter : n / 4 < p) (hpthird : p ≤ n / 3)
    (hqquarter : n / 4 < q) (hqthird : q ≤ n / 3) :
    NonCoprimeChain
      (orderedPrimeClass n p (2 * p) (3 * p) ++
       orderedPrimeClass n q (3 * q) (2 * q)) := by sorry
