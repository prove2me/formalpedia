-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_m_mul_le_nu
-- name    : SemigroupBetti.GenData.m_mul_le_nu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:18.480881+00:00
-- url     : https://prove2.me/theorems/461cb480-b9fd-5693-a7ec-476613aa3aba
-- title:
--   Gen Data: m mul le nu
-- statement:
--   The Gen Data construction uses the m mul le nu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L142-L144
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L142-L144

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

theorem SemigroupBetti.GenData.m_mul_le_nu (z : Fin 4 → ℕ) (i : Fin 4) : G.m * z i ≤ G.nu z := by sorry
