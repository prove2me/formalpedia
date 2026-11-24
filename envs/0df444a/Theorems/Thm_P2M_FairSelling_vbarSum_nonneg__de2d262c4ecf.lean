-- Prove2me | Theorems.Thm_P2M_FairSelling_vbarSum_nonneg__de2d262c4ecf
-- name    : P2M_FairSelling_vbarSum_nonneg__de2d262c4ecf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:52.702976+00:00
-- url     : https://prove2.me/theorems/5a857bf6-807e-43d2-870d-056476b598fa
-- title:
--   P2 M Fair Selling vbar Sum nonneg  de2d262c4ecf: P2 M Fair Selling vbar Sum nonneg  de2d262c4ecf
-- statement:
--   `v̄` of a bundle is non-negative.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L45-L47
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L45-L47

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]

theorem P2M_FairSelling_vbarSum_nonneg__de2d262c4ecf (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (Y : Finset G) :
    0 ≤ vbarSum w p Y := by sorry

alias «FairSelling».«vbarSum_nonneg'» := P2M_FairSelling_vbarSum_nonneg__de2d262c4ecf
