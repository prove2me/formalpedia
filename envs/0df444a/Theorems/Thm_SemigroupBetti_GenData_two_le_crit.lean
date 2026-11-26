-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_two_le_crit
-- name    : SemigroupBetti.GenData.two_le_crit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:06:56.04386+00:00
-- url     : https://prove2.me/theorems/c5227f88-2328-544c-8513-1b944a620661
-- title:
--   Gen Data: two le crit
-- statement:
--   **Lemma 3.5.** Under generator minimality, `cᵢ ≥ 2`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L232-L238
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L232-L238

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

theorem SemigroupBetti.GenData.two_le_crit (i : Fin 4) : 2 ≤ G.crit i := by sorry
