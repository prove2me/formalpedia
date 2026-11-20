-- Prove2me | Theorems.Thm_P010_classConcat_nodup
-- name    : P010.classConcat_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:34:52.737004+00:00
-- url     : https://prove2.me/theorems/a97d3894-a267-478c-9ccc-1d0258c87d09
-- title:
--   P010: class Concat nodup
-- statement:
--   Concatenating distinct prime-factor classes never repeats
--   a vertex.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1755-L1762
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1755-L1762

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.classConcat_nodup (n : ℕ) (ps : List ℕ) (hps : ps.Nodup) :
    (classConcat n ps).Nodup := by sorry
