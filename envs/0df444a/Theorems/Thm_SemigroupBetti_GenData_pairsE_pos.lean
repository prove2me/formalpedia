-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_pairsE_pos
-- name    : SemigroupBetti.GenData.pairsE_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:04:13.144804+00:00
-- url     : https://prove2.me/theorems/fe4d1bb7-877a-42d3-b851-fc9df8072006
-- title:
--   Gen Data: pairs E pos
-- statement:
--   The Gen Data construction uses the pairs E pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L258-L263
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L258-L263

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.pairsE_pos : ∀ x ∈ G.pairsE, 1 ≤ x.1 ∧ 1 ≤ x.2 := by sorry
