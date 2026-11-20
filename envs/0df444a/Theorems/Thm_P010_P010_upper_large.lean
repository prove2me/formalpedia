-- Prove2me | Theorems.Thm_P010_P010_upper_large
-- name    : P010.P010_upper_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:42:57.254076+00:00
-- url     : https://prove2.me/theorems/2d15b781-ab3e-4e94-8697-6c8237077ccf
-- title:
--   P010: P010 upper large
-- statement:
--   For every n≥12, there is an optimal permutation of [1,n]
--   attaining the exact target number of coprime adjacencies.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2288-L2305
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2288-L2305

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.P010_upper_large (n : ℕ) (hn : 12 ≤ n) :
    ∃ a : List ℕ, IsPermutation n a ∧
      adjacentCount a ≤ target n := by sorry
