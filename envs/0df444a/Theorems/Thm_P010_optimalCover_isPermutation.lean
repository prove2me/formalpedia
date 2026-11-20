-- Prove2me | Theorems.Thm_P010_optimalCover_isPermutation
-- name    : P010.optimalCover_isPermutation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:42:07.435699+00:00
-- url     : https://prove2.me/theorems/fc46eb24-9ebb-4a7e-abe3-679107836ee0
-- title:
--   P010: optimal Cover is Permutation
-- statement:
--   The assembled cover uses each integer in [1,n] exactly once.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2236-L2284
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2236-L2284

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.optimalCover_isPermutation (n : ℕ) (hn : 12 ≤ n) :
    IsPermutation n (optimalCover n).flatten := by sorry
