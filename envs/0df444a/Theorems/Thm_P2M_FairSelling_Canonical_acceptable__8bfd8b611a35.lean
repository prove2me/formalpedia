-- Prove2me | Theorems.Thm_P2M_FairSelling_Canonical_acceptable__8bfd8b611a35
-- name    : P2M_FairSelling_Canonical_acceptable__8bfd8b611a35
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:31.204609+00:00
-- url     : https://prove2.me/theorems/3643e084-2e07-4800-ae96-6ff37ceb437e
-- title:
--   P2 M Fair Selling Canonical acceptable  8bfd8b611a35: P2 M Fair Selling Canonical acceptable  8bfd8b611a35
-- statement:
--   The P2 M Fair Selling Canonical acceptable  8bfd8b611a35 construction uses the P2 M Fair Selling Canonical acceptable  8bfd8b611a35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L212-L215
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L212-L215

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.Canonical
variable {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
omit [Fintype G]

theorem P2M_FairSelling_Canonical_acceptable__8bfd8b611a35 (C : Canonical w p μ t k R D) (j : Fin k) :
    t ≤ vbarSum w p (C.goods j) + C.cash j := by sorry

alias «FairSelling».«Canonical».«acceptable'» := P2M_FairSelling_Canonical_acceptable__8bfd8b611a35
