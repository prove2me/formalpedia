-- Prove2me | Theorems.Thm_P010_segments_index_perm
-- name    : P010.segments_index_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:41:59.704177+00:00
-- url     : https://prove2.me/theorems/dea47509-cfdc-4bca-a380-8db0e96eb924
-- title:
--   P010: segments index perm
-- statement:
--   Every prime ≤ n belongs to exactly one of the core, middle,
--   or large prime-index ranges.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2143-L2173
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2143-L2173

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.segments_index_perm (n : ℕ) :
    ((n / 3).primesLE.toList ++
      (middlePrimes n).toList ++
      (largePrimes n).toList).Perm n.primesLE.toList := by sorry
