-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_m_le_n
-- name    : SemigroupBetti.GenData.m_le_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:26:17.441603+00:00
-- url     : https://prove2.me/theorems/d2274f44-fdcb-4680-b030-b17a530cb25f
-- title:
--   Gen Data: m le n
-- statement:
--   The Gen Data construction uses the m le n property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L110-L111
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L110-L111

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

theorem SemigroupBetti.GenData.m_le_n (i : Fin 4) : G.m ≤ G.n i := by sorry
