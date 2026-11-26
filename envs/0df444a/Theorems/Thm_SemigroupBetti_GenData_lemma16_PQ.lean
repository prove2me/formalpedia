-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_lemma16_PQ
-- name    : SemigroupBetti.GenData.lemma16_PQ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:06:50.648307+00:00
-- url     : https://prove2.me/theorems/ce88bb89-8c78-44fb-acdd-e2edb36bee3a
-- title:
--   Gen Data: lemma16 PQ
-- statement:
--   **Lemma 16.** If `(A, B) = (1, W - 1)` then `P + Q ≤ 2W - 5`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L274-L290
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L274-L290

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

theorem SemigroupBetti.GenData.lemma16_PQ (hA : G.A = 1) (hB : G.B = G.W - 1) : G.P + G.Q ≤ 2 * G.W - 5 := by sorry
