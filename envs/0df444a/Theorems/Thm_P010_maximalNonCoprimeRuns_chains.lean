-- Prove2me | Theorems.Thm_P010_maximalNonCoprimeRuns_chains
-- name    : P010.maximalNonCoprimeRuns_chains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:50.468311+00:00
-- url     : https://prove2.me/theorems/47e726b4-108b-4b5f-bc8a-2cc7bf36d221
-- title:
--   P010: maximal Non Coprime Runs chains
-- statement:
--   Every component of the canonical cut decomposition is a
--   non-coprime path, with no appeal to the submitted construction.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L357-L364
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L357-L364

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.maximalNonCoprimeRuns_chains (a : List ℕ) :
    ∀ p ∈ maximalNonCoprimeRuns a, NonCoprimeChain p := by sorry
