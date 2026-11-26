-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_E_le
-- name    : SemigroupBetti.GenData.E_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:27.750587+00:00
-- url     : https://prove2.me/theorems/3fe282b9-1791-428c-a227-ab045d138b6a
-- title:
--   Gen Data: E le
-- statement:
--   **Lemma 12.** `E ≤ p + q - 1`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L266-L275
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L266-L275

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

theorem SemigroupBetti.GenData.E_le : G.E ≤ G.p + G.q - 1 := by sorry
