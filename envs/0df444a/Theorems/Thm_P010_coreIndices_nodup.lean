-- Prove2me | Theorems.Thm_P010_coreIndices_nodup
-- name    : P010.coreIndices_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:51.733144+00:00
-- url     : https://prove2.me/theorems/012880c0-e0c1-461c-908a-063865cc3ba8
-- title:
--   P010: core Indices nodup
-- statement:
--   The P010 construction uses the core Indices nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1822-L1844
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1822-L1844

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.coreIndices_nodup (n : ℕ) (hn : 12 ≤ n) :
    (coreIndices n).Nodup := by sorry
