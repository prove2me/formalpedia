-- Prove2me | Theorems.Thm_P010_P010_exact
-- name    : P010.P010_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:35:24.06591+00:00
-- url     : https://prove2.me/theorems/4d748e95-07cc-4cfa-a63c-d2b53b419cb7
-- title:
--   P010: P010 exact
-- statement:
--   The exact theorem submitted to Integers, for every n≥4.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2308-L2317
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2308-L2317

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.P010_exact (n : ℕ) (hn : 4 ≤ n) :
    h n = target n := by sorry
