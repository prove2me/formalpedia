-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_isSplit_of_mem_fam
-- name    : SemigroupBetti.GenData.isSplit_of_mem_fam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:55:15.959625+00:00
-- url     : https://prove2.me/theorems/054b5967-dbd2-4eeb-a998-504948d2300e
-- title:
--   Gen Data: is Split of mem fam
-- statement:
--   The Gen Data construction uses the is Split of mem fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L162-L163
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L162-L163

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.isSplit_of_mem_fam {K : Finset (Fin 4)} {d : ℕ} (h : d ∈ G.fam K) : G.IsSplit d K := by sorry
