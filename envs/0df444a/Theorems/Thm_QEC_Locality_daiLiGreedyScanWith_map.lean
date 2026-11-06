-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGreedyScanWith_map
-- name    : QEC.Locality.daiLiGreedyScanWith_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:59:17.56208+00:00
-- url     : https://prove2.me/theorems/1929813c-7cb8-41fa-8818-b16879bec46f
-- title:
--   Locality: dai Li Greedy Scan With map
-- statement:
--   The payload scan has exactly the same counter trace as the Nat kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L893-L931
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L893-L931

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.daiLiGreedyScanWith_map {α : Type*} (weight : α → Nat) (d : Nat) :
    ∀ (remaining pending : List α) (emitted : List (List α)),
      (daiLiGreedyScanWith weight d remaining pending emitted).map (List.map weight) =
        daiLiGreedyScan d (remaining.map weight) (pending.map weight)
          (emitted.map (List.map weight)) := by sorry
