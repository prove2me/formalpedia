-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_card_compl_of_card_two
-- name    : SemigroupBetti.GenData.card_compl_of_card_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:56:45.483578+00:00
-- url     : https://prove2.me/theorems/68a44aa8-7bdd-47e4-ad88-ef27cb1a098b
-- title:
--   Gen Data: card compl of card two
-- statement:
--   The Gen Data construction uses the card compl of card two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L218-L219
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L218-L219

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.card_compl_of_card_two {K : Finset (Fin 4)} (hK : K.card = 2) : Kᶜ.card = 2 := by sorry
