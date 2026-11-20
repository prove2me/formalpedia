-- Prove2me | Theorems.Thm_P010_packLeafClasses_length
-- name    : P010.packLeafClasses_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:48.93909+00:00
-- url     : https://prove2.me/theorems/005207c3-f1ee-4573-9b0f-4bda34c09a2d
-- title:
--   P010: pack Leaf Classes length
-- statement:
--   Pair packing creates the exact required number of nonisolated
--   paths, regardless of how many leaf-prime classes are present.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1426-L1443
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1426-L1443

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.packLeafClasses_length (core : List ℕ) :
    ∀ leafs : List ℕ,
      (packLeafClasses core leafs).length =
        max 1 ((leafs.length + 1) / 2) := by sorry
