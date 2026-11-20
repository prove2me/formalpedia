-- Prove2me | Theorems.Thm_P010_classConcat_toFinset
-- name    : P010.classConcat_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:35.886189+00:00
-- url     : https://prove2.me/theorems/0f66d770-5ec7-4ede-8522-9be6113dcdb9
-- title:
--   P010: class Concat to Finset
-- statement:
--   The union of prime-factor classes indexed by ps is precisely
--   the set of vertices occurring in their concatenated lists.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1774-L1779
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1774-L1779

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.classConcat_toFinset (n : ℕ) (ps : List ℕ) :
    (classConcat n ps).toFinset =
      ps.toFinset.biUnion (primeClass n) := by sorry
