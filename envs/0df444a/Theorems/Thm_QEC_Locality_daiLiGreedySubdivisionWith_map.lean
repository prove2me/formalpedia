-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGreedySubdivisionWith_map
-- name    : QEC.Locality.daiLiGreedySubdivisionWith_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:50:08.664313+00:00
-- url     : https://prove2.me/theorems/51bfcc14-bbbc-48ce-97bb-c5300836bc9f
-- title:
--   Locality: dai Li Greedy Subdivision With map
-- statement:
--   The payload subdivision maps exactly to the established Nat subdivision.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L934-L939
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L934-L939

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

theorem QEC.Locality.daiLiGreedySubdivisionWith_map {α : Type*} (weight : α → Nat) (d : Nat)
    (bands : List α) :
    (daiLiGreedySubdivisionWith weight d bands).map (List.map weight) =
      daiLiGreedyAtomicSubdivision d (bands.map weight) := by sorry
