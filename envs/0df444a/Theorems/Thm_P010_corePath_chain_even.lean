-- Prove2me | Theorems.Thm_P010_corePath_chain_even
-- name    : P010.corePath_chain_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:46.268385+00:00
-- url     : https://prove2.me/theorems/bf753c40-ec85-42f2-a4fd-01b37dd919b6
-- title:
--   P010: core Path chain even
-- statement:
--   The assembled core path is nonempty, noncoprime, and even-ended,
--   with no appeal to the Landau prime-counting inequality.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1721-L1727
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1721-L1727

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.corePath_chain_even (n : ℕ) (hn : 12 ≤ n) :
    NonCoprimeChain (corePath n) ∧ EvenEnded (corePath n) := by sorry
