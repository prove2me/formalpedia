-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_alt_coord_eq_zero
-- name    : SemigroupBetti.GenData.alt_coord_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:53:43.112775+00:00
-- url     : https://prove2.me/theorems/8679ef25-d29b-4a44-91f6-a2f2543c8565
-- title:
--   Gen Data: alt coord eq zero
-- statement:
--   **Lemma 3.2.** Every alternative factorization at the critical degree avoids `i`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L78-L111
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L78-L111

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

theorem SemigroupBetti.GenData.alt_coord_eq_zero {i : Fin 4} {y : Fin 4 → ℕ} (hy : G.nu y = G.crit i * G.n i)
    (hne : y ≠ Pi.single i (G.crit i)) : y i = 0 := by sorry
