-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_card_genSet_le
-- name    : SemigroupBetti.GenData.card_genSet_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:36.622798+00:00
-- url     : https://prove2.me/theorems/646fdd9e-1b02-5dff-87bc-907807adf82d
-- title:
--   Gen Data: card gen Set le
-- statement:
--   The Gen Data construction uses the card gen Set le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L122-L128
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L122-L128

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]

theorem SemigroupBetti.GenData.card_genSet_le (d : ℕ) : #(G.genSet K d) ≤ G.ncomp d - 1 := by sorry
