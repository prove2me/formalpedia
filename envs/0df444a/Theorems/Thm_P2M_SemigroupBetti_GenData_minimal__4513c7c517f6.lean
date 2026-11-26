-- Prove2me | Theorems.Thm_P2M_SemigroupBetti_GenData_minimal__4513c7c517f6
-- name    : P2M_SemigroupBetti_GenData_minimal__4513c7c517f6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:42.531342+00:00
-- url     : https://prove2.me/theorems/2f629937-0dfe-4d5d-bdc3-9bc229c84891
-- title:
--   P2 M Semigroup Betti Gen Data minimal  4513c7c517f6: P2 M Semigroup Betti Gen Data minimal  4513c7c517f6
-- statement:
--   The P2 M Semigroup Betti Gen Data minimal  4513c7c517f6 construction uses the P2 M Semigroup Betti Gen Data minimal  4513c7c517f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L92-L93
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L92-L93

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

theorem P2M_SemigroupBetti_GenData_minimal__4513c7c517f6 (i : Fin 4) (z : Fin 4 → ℕ) (hz : z i = 0) : G.nu z ≠ G.n i := by sorry

alias «SemigroupBetti».«GenData».«minimal'» := P2M_SemigroupBetti_GenData_minimal__4513c7c517f6
