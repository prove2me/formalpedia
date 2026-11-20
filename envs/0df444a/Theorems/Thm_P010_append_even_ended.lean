-- Prove2me | Theorems.Thm_P010_append_even_ended
-- name    : P010.append_even_ended
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:39:12.096645+00:00
-- url     : https://prove2.me/theorems/965d642e-0c99-4d33-9829-519982efefe4
-- title:
--   P010: append even ended
-- statement:
--   Concatenating two even-ended noncoprime paths preserves the
--   noncoprime-chain property and both even endpoints.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1313-L1335
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1313-L1335

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.append_even_ended (a b : List ℕ)
    (ha : NonCoprimeChain a) (hb : NonCoprimeChain b)
    (hea : EvenEnded a) (heb : EvenEnded b) :
    NonCoprimeChain (a ++ b) ∧ EvenEnded (a ++ b) := by sorry
