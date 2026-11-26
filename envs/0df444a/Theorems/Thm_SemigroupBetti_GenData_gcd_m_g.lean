-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_gcd_m_g
-- name    : SemigroupBetti.GenData.gcd_m_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:09.78315+00:00
-- url     : https://prove2.me/theorems/05ee424a-17c9-4d74-b8b2-1754d4030334
-- title:
--   Gen Data: gcd m g
-- statement:
--   The Gen Data construction uses the gcd m g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L195-L195
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L195-L195

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

theorem SemigroupBetti.GenData.gcd_m_g : Nat.gcd G.m G.g = 1 := by sorry
