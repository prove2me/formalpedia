-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_Q_le
-- name    : SemigroupBetti.GenData.Q_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:18.943222+00:00
-- url     : https://prove2.me/theorems/1855e4e2-0db7-5bf6-b50b-be3070713301
-- title:
--   Gen Data: Q le
-- statement:
--   **Lemma 10.** `Q ≤ R - 1`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L180-L191
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L180-L191

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

theorem SemigroupBetti.GenData.Q_le : G.Q ≤ G.R - 1 := by sorry
