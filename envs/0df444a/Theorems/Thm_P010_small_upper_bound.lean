-- Prove2me | Theorems.Thm_P010_small_upper_bound
-- name    : P010.small_upper_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:35:55.972661+00:00
-- url     : https://prove2.me/theorems/3a12e8cf-0754-45f1-8057-bc617b8294bb
-- title:
--   P010: small upper bound
-- statement:
--   The P010 construction uses the small upper bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L199-L203
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean#L199-L203

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
set_option autoImplicit true
@[expose] public section
public section
open P010

theorem P010.small_upper_bound (n : ℕ) (hn4 : 4 ≤ n) (hn11 : n ≤ 11) :
    ∃ a : List ℕ, IsPermutation n a ∧ adjacentCount a = target n := by sorry
