-- Prove2me | Theorems.Thm_SemigroupBetti_mem_supp
-- name    : SemigroupBetti.mem_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:26.621961+00:00
-- url     : https://prove2.me/theorems/5e7be4d9-096b-4047-b0ac-24daa13528c1
-- title:
--   Semigroup Betti: mem supp
-- statement:
--   The Semigroup Betti construction uses the mem supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L51-L52
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L51-L52

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset

theorem SemigroupBetti.mem_supp {z : Fin 4 → ℕ} {i : Fin 4} : i ∈ supp z ↔ 0 < z i := by sorry
