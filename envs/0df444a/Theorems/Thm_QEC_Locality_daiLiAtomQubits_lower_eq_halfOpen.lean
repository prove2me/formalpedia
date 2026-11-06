-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomQubits_lower_eq_halfOpen
-- name    : QEC.Locality.daiLiAtomQubits_lower_eq_halfOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:51:39.273027+00:00
-- url     : https://prove2.me/theorems/912b92d1-b177-4a1d-b6eb-117eb27a7764
-- title:
--   Locality: dai Li Atom Qubits lower eq half Open
-- statement:
--   A globally support-free lower atom is exactly the half-open lower slice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L367-L396
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L367-L396

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

theorem QEC.Locality.daiLiAtomQubits_lower_eq_halfOpen
    (embedding : UnitSeparatedEmbedding2D ι) (left right lower cut upper : ℝ)
    (hLowerCut : lower < cut) (hCutUpper : cut < upper)
    (hCutFree : cut ∉ daiLiGlobalVerticalQubitSupport embedding) :
    daiLiAtomQubits embedding left right (lower, cut) =
      daiLiBelowHorizontalCut embedding (left, lower) (right, upper) cut := by sorry
