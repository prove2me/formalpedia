-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGreedySubdivisionWith_join
-- name    : QEC.Locality.daiLiGreedySubdivisionWith_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:27.287965+00:00
-- url     : https://prove2.me/theorems/7cab76a9-d2ec-49bf-8a00-f08d2c6ac859
-- title:
--   Locality: dai Li Greedy Subdivision With join
-- statement:
--   The payload subdivision covers its atoms in their original finite order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L968-L971
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L968-L971

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

theorem QEC.Locality.daiLiGreedySubdivisionWith_join {α : Type*} (weight : α → Nat) (d : Nat)
    (bands : List α) :
    (daiLiGreedySubdivisionWith weight d bands).flatten = bands := by sorry
