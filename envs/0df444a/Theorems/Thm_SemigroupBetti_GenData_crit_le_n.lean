-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_crit_le_n
-- name    : SemigroupBetti.GenData.crit_le_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:06:49.443098+00:00
-- url     : https://prove2.me/theorems/c6cdcda8-62fc-4fdc-8201-dafacdcfb207
-- title:
--   Gen Data: crit le n
-- statement:
--   **Lemma 3.1.** `cᵢ ≤ nⱼ` for every `j ≠ i`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L70-L71
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L70-L71

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

theorem SemigroupBetti.GenData.crit_le_n {i j : Fin 4} (hji : j ≠ i) : G.crit i ≤ G.n j := by sorry
