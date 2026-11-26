-- Prove2me | Theorems.Thm_SemigroupBetti_sharesVar_comm
-- name    : SemigroupBetti.sharesVar_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:31.06182+00:00
-- url     : https://prove2.me/theorems/c4af312e-5543-42d1-a0c2-88801fa8f8d1
-- title:
--   Semigroup Betti: shares Var comm
-- statement:
--   The Semigroup Betti construction uses the shares Var comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L57-L58
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L57-L58

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset

theorem SemigroupBetti.sharesVar_comm {z z' : Fin 4 → ℕ} : SharesVar z z' ↔ SharesVar z' z := by sorry
