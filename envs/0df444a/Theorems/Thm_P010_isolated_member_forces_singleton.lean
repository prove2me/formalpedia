-- Prove2me | Theorems.Thm_P010_isolated_member_forces_singleton
-- name    : P010.isolated_member_forces_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:32:56.643709+00:00
-- url     : https://prove2.me/theorems/1aea6561-0d51-4ceb-85bf-f9ed025acdce
-- title:
--   P010: isolated member forces singleton
-- statement:
--   In a simple non-coprime path, a vertex coprime to all other
--   vertices of the path can occur only as a singleton path.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L491-L537
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L491-L537

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.isolated_member_forces_singleton (p : ℕ) :
    ∀ a : List ℕ, NonCoprimeChain a → a.Nodup →
      p ∈ a → (∀ x ∈ a, x ≠ p → Nat.Coprime p x) → a = [p] := by sorry
