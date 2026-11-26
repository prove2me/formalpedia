-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_gcd_ABW
-- name    : SemigroupBetti.GenData.gcd_ABW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:00.781961+00:00
-- url     : https://prove2.me/theorems/220ed99d-8946-576c-bb72-10227f7dc631
-- title:
--   Gen Data: gcd ABW
-- statement:
--   The Gen Data construction uses the gcd ABW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L189-L193
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L189-L193

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

theorem SemigroupBetti.GenData.gcd_ABW : Nat.gcd G.A (Nat.gcd G.B G.W) = 1 := by sorry
