-- Prove2me | Theorems.Thm_SemigroupBetti_SharesVar_symm
-- name    : SemigroupBetti.SharesVar.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:25.647093+00:00
-- url     : https://prove2.me/theorems/9d1a59d3-066f-5f8a-a4b9-07502d478157
-- title:
--   Shares Var: symm
-- statement:
--   The Shares Var construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L54-L55
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L54-L55

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset

theorem SemigroupBetti.SharesVar.symm {z z' : Fin 4 → ℕ} (h : SharesVar z z') : SharesVar z' z := by sorry
