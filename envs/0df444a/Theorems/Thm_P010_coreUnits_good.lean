-- Prove2me | Theorems.Thm_P010_coreUnits_good
-- name    : P010.coreUnits_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:40.634489+00:00
-- url     : https://prove2.me/theorems/b71c5e70-fbde-433a-8f92-898e3c3a0f91
-- title:
--   P010: core Units good
-- statement:
--   Every unit of the core is a noncoprime even-ended path.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1689-L1717
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1689-L1717

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.coreUnits_good (n : ℕ) (hn : 12 ≤ n) :
    ∀ unit ∈ coreUnits n, NonCoprimeChain unit ∧ EvenEnded unit := by sorry
