-- Prove2me | Theorems.Thm_P010_flatten_even_ended_units
-- name    : P010.flatten_even_ended_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:40:00.280226+00:00
-- url     : https://prove2.me/theorems/57b9cf58-eee7-4dd9-bcad-362bb7b82669
-- title:
--   P010: flatten even ended units
-- statement:
--   Any nonempty list of even-ended noncoprime paths can be flattened
--   to a single even-ended noncoprime path.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1528-L1552
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L1528-L1552

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.flatten_even_ended_units :
    ∀ units : List (List ℕ), units ≠ [] →
      (∀ unit ∈ units, NonCoprimeChain unit ∧ EvenEnded unit) →
      NonCoprimeChain units.flatten ∧ EvenEnded units.flatten := by sorry
