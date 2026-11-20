-- Prove2me | Theorems.Thm_P010_one_Icc_two_perm_Icc_one
-- name    : P010.one_Icc_two_perm_Icc_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:42:06.923931+00:00
-- url     : https://prove2.me/theorems/40e7ed7a-8f22-41c1-a39b-a5356a3bd5ea
-- title:
--   P010: one Icc two perm Icc one
-- statement:
--   Adding vertex 1 to the interval [2,n] gives a permutation of
--   the interval [1,n], for n≥1.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2224-L2233
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2224-L2233

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.one_Icc_two_perm_Icc_one (n : ℕ) (hn : 1 ≤ n) :
    (1 :: (Finset.Icc 2 n).toList).Perm
      (Finset.Icc 1 n).toList := by sorry
