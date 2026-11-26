-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_pairsE_injOn
-- name    : SemigroupBetti.GenData.pairsE_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:03:50.114421+00:00
-- url     : https://prove2.me/theorems/01b6d64c-fbcf-5600-91d5-8a48ca492dea
-- title:
--   Gen Data: pairs E inj On
-- statement:
--   The Gen Data construction uses the pairs E inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L237-L244
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L237-L244

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

theorem SemigroupBetti.GenData.pairsE_injOn : Set.InjOn (fun d => (G.sel d {1, 2} 1, G.sel d {1, 2} 2)) G.famE := by sorry
