-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomicPiecesMass_eq_flattenMass
-- name    : QEC.Locality.daiLiAtomicPiecesMass_eq_flattenMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:49:06.012279+00:00
-- url     : https://prove2.me/theorems/eae109af-9e9f-41da-a42b-dbea72b0bd02
-- title:
--   Locality: dai Li Atomic Pieces Mass eq flatten Mass
-- statement:
--   The Locality construction uses the dai Li Atomic Pieces Mass eq flatten Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L637-L647
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L637-L647

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

theorem QEC.Locality.daiLiAtomicPiecesMass_eq_flattenMass (pieces : List (List DaiLiAtomicCounter)) :
    daiLiAtomicPiecesMass pieces = daiLiAtomicMass pieces.flatten := by sorry
