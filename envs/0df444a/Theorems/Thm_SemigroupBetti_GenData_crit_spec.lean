-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_crit_spec
-- name    : SemigroupBetti.GenData.crit_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:54:04.417107+00:00
-- url     : https://prove2.me/theorems/cd4f5efc-73aa-4718-8e20-5bc09c009065
-- title:
--   Gen Data: crit spec
-- statement:
--   The Gen Data construction uses the crit spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L62-L62
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L62-L62

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

theorem SemigroupBetti.GenData.crit_spec (i : Fin 4) : G.IsCritCand i (G.crit i) := by sorry
