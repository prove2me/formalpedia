-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_pairsE_antichain
-- name    : SemigroupBetti.GenData.pairsE_antichain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:03:57.454857+00:00
-- url     : https://prove2.me/theorems/38b65aa6-252f-5e50-aa31-77ff38bd0bb7
-- title:
--   Gen Data: pairs E antichain
-- statement:
--   The Gen Data construction uses the pairs E antichain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L248-L256
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L248-L256

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

theorem SemigroupBetti.GenData.pairsE_antichain : IsPairAntichain G.pairsE := by sorry
