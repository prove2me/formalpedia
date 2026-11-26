-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_two_le_W_sub_A
-- name    : SemigroupBetti.GenData.two_le_W_sub_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:53.059971+00:00
-- url     : https://prove2.me/theorems/d7515e46-a1ad-50fd-a918-b317ede31514
-- title:
--   Gen Data: two le W sub A
-- statement:
--   The Gen Data construction uses the two le W sub A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L186-L187
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L186-L187

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

theorem SemigroupBetti.GenData.two_le_W_sub_A : 2 ≤ G.W - G.A := by sorry
