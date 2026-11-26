-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_q_pos
-- name    : SemigroupBetti.GenData.q_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:32.932234+00:00
-- url     : https://prove2.me/theorems/8a6357e7-669b-42d8-a079-3e05aabba81b
-- title:
--   Gen Data: q pos
-- statement:
--   The Gen Data construction uses the q pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L52-L56
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L52-L56

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.q_pos : 1 ≤ G.q := by sorry
