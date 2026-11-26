-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_beta1_le_two_W_of_ne
-- name    : SemigroupBetti.GenData.beta1_le_two_W_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:04:30.312227+00:00
-- url     : https://prove2.me/theorems/6c19a354-0659-5c33-94db-22f66cffcbb4
-- title:
--   Gen Data: beta1 le two W of ne
-- statement:
--   **Lemma 13.** If `(s,t) ≠ (1,1)` then `β₁ ≤ 2W`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Arith.lean#L50-L75
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Arith.lean#L50-L75

module
public import Definitions.Def_SemigroupBetti_Antichain
public import Definitions.Def_SemigroupBetti_Arith
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.beta1_le_two_W_of_ne (h : (G.s, G.t) ≠ (1, 1)) : G.beta1 ≤ 2 * G.W := by sorry
