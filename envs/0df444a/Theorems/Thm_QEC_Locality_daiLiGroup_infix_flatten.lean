-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGroup_infix_flatten
-- name    : QEC.Locality.daiLiGroup_infix_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:21.876973+00:00
-- url     : https://prove2.me/theorems/4b5e5d83-5876-4d2c-acca-b2a3bb7739de
-- title:
--   Locality: dai Li Group infix flatten
-- statement:
--   A member of a list of lists is a contiguous infix of its flattening.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1048-L1058
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1048-L1058

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

theorem QEC.Locality.daiLiGroup_infix_flatten {α : Type*}
    (groups : List (List α)) (piece : List α) (hPiece : piece ∈ groups) :
    piece <:+: groups.flatten := by sorry
