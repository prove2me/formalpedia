-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_lemma14
-- name    : SemigroupBetti.GenData.lemma14
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:06:03.188403+00:00
-- url     : https://prove2.me/theorems/59ad086a-03a4-563f-8502-9f9e33b041ac
-- title:
--   Gen Data: lemma14
-- statement:
--   **Lemma 14.** If `A = 1`, `B = W - 1` and `P = W - 2`, then `c₂ = W - 1`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L163-L226
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L163-L226

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.lemma14 (hA : G.A = 1) (hB : G.B = G.W - 1) (hP : G.P = G.W - 2) :
    G.crit 2 = G.W - 1 := by sorry
