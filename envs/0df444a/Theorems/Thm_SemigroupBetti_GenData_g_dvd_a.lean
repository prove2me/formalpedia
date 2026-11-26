-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_g_dvd_a
-- name    : SemigroupBetti.GenData.g_dvd_a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:26:37.13571+00:00
-- url     : https://prove2.me/theorems/f3021a82-d701-522b-a59a-36219a224da7
-- title:
--   Gen Data: g dvd a
-- statement:
--   The Gen Data construction uses the g dvd a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L161-L161
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L161-L161

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

theorem SemigroupBetti.GenData.g_dvd_a : G.g ∣ G.a := by sorry
