-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGreedyAtomicSubdivision_join
-- name    : QEC.Locality.daiLiGreedyAtomicSubdivision_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:49:59.770877+00:00
-- url     : https://prove2.me/theorems/4a98c9ee-8d57-4185-a15a-b383fd6e6190
-- title:
--   Locality: dai Li Greedy Atomic Subdivision join
-- statement:
--   The concrete greedy subdivision covers its atoms in their original order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L814-L816
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L814-L816

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

theorem QEC.Locality.daiLiGreedyAtomicSubdivision_join (d : Nat) (bands : List DaiLiAtomicCounter) :
    (daiLiGreedyAtomicSubdivision d bands).flatten = bands := by sorry
