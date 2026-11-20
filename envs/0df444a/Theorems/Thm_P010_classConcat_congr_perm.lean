-- Prove2me | Theorems.Thm_P010_classConcat_congr_perm
-- name    : P010.classConcat_congr_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:34:57.260212+00:00
-- url     : https://prove2.me/theorems/cef7ec8e-40ac-48bf-8488-81ef2bf97512
-- title:
--   P010: class Concat congr perm
-- statement:
--   Reordering the indices merely permutes the concatenated class
--   catalog.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1766-L1770
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1766-L1770

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.classConcat_congr_perm (n : ℕ) (ps qs : List ℕ)
    (hpq : ps.Perm qs) :
    (classConcat n ps).Perm (classConcat n qs) := by sorry
