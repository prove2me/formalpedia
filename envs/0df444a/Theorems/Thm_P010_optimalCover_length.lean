-- Prove2me | Theorems.Thm_P010_optimalCover_length
-- name    : P010.optimalCover_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:42:07.968032+00:00
-- url     : https://prove2.me/theorems/c301bf06-8b07-4ce5-838f-b88bf9e6d978
-- title:
--   P010: optimal Cover length
-- statement:
--   The cover has exactly the number of components prescribed
--   by the P010 formula, plus the singleton vertex 1.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2211-L2220
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L2211-L2220

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.optimalCover_length (n : ℕ) :
    (optimalCover n).length =
      1 + (largePrimes n).card +
        max 1 (((middlePrimes n).card + 1) / 2) := by sorry
