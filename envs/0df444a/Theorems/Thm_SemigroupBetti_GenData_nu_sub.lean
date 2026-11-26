-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_nu_sub
-- name    : SemigroupBetti.GenData.nu_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:02.987958+00:00
-- url     : https://prove2.me/theorems/1ee9ca54-3775-5ebf-99fd-05a6f41b8921
-- title:
--   Gen Data: nu sub
-- statement:
--   If `x ≤ y` coordinatewise then `ν(y) = ν(x) + ν(y - x)`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L132-L135
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L132-L135

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.nu_sub {x y : Fin 4 → ℕ} (h : x ≤ y) : G.nu y = G.nu x + G.nu (y - x) := by sorry
