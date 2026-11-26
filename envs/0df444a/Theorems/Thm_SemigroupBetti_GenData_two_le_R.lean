-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_two_le_R
-- name    : SemigroupBetti.GenData.two_le_R
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:02.007624+00:00
-- url     : https://prove2.me/theorems/7fe57421-67a8-486a-8ec7-6ca2c196b67e
-- title:
--   Gen Data: two le R
-- statement:
--   The Gen Data construction uses the two le R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L66-L67
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L66-L67

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.two_le_R : 2 ≤ G.R := by sorry
