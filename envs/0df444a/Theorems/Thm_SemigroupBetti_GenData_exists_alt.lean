-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exists_alt
-- name    : SemigroupBetti.GenData.exists_alt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:53:52.676871+00:00
-- url     : https://prove2.me/theorems/c74b3088-fec9-49f2-8061-ccf7e1ec9a8b
-- title:
--   Gen Data: exists alt
-- statement:
--   The Gen Data construction uses the exists alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L73-L75
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L73-L75

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

theorem SemigroupBetti.GenData.exists_alt (i : Fin 4) :
    ∃ y : Fin 4 → ℕ, G.nu y = G.crit i * G.n i ∧ y ≠ Pi.single i (G.crit i) := by sorry
