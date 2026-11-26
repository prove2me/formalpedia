-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_one_le_crit
-- name    : SemigroupBetti.GenData.one_le_crit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:53:39.442435+00:00
-- url     : https://prove2.me/theorems/524b1920-293a-4bef-a2d6-e48a0ac76881
-- title:
--   Gen Data: one le crit
-- statement:
--   **Lemma 3.1.** `1 ≤ cᵢ`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L67-L67
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L67-L67

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.one_le_crit (i : Fin 4) : 1 ≤ G.crit i := by sorry
