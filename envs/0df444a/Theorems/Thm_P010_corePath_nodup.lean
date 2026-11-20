-- Prove2me | Theorems.Thm_P010_corePath_nodup
-- name    : P010.corePath_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:49:55.230701+00:00
-- url     : https://prove2.me/theorems/32f846af-696b-44e2-b8ca-4ad720687706
-- title:
--   P010: core Path nodup
-- statement:
--   No vertex is repeated in the core path.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2052-L2056
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2052-L2056

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.corePath_nodup (n : ℕ) (hn : 12 ≤ n) :
    (corePath n).Nodup := by sorry
