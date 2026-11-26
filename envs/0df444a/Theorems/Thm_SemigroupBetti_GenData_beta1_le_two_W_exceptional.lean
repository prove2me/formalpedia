-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_beta1_le_two_W_exceptional
-- name    : SemigroupBetti.GenData.beta1_le_two_W_exceptional
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:06:37.517277+00:00
-- url     : https://prove2.me/theorems/7535685c-8a39-4c70-af32-c7313d7e74ce
-- title:
--   Gen Data: beta1 le two W exceptional
-- statement:
--   **Lemma 16.** If `(A, B) = (1, W - 1)` then `β₁ ≤ 2W`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L293-L301
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L293-L301

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

theorem SemigroupBetti.GenData.beta1_le_two_W_exceptional (hA : G.A = 1) (hB : G.B = G.W - 1) :
    G.beta1 ≤ 2 * G.W := by sorry
