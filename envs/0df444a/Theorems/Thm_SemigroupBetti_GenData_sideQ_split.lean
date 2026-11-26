-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sideQ_split
-- name    : SemigroupBetti.GenData.sideQ_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:24.753333+00:00
-- url     : https://prove2.me/theorems/84035e52-d1a2-4aea-ba03-7cd2e0c60931
-- title:
--   Gen Data: side Q split
-- statement:
--   The Gen Data construction uses the side Q split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L158-L160
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L158-L160

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

theorem SemigroupBetti.GenData.sideQ_split {d : ℕ} (hd : d ∈ G.famQ) : G.IsSplit d {1, 3} := by sorry
