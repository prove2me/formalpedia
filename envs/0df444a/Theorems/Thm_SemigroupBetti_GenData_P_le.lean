-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_P_le
-- name    : SemigroupBetti.GenData.P_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:46.807171+00:00
-- url     : https://prove2.me/theorems/8e3753f4-5ab0-42a6-8cd9-6e2e9ca18812
-- title:
--   Gen Data: P le
-- statement:
--   **Lemma 10.** `P ≤ R - 1`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L166-L177
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L166-L177

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

theorem SemigroupBetti.GenData.P_le : G.P ≤ G.R - 1 := by sorry
