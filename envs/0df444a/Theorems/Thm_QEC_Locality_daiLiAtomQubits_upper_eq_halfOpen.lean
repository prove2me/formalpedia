-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomQubits_upper_eq_halfOpen
-- name    : QEC.Locality.daiLiAtomQubits_upper_eq_halfOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:51:16.081029+00:00
-- url     : https://prove2.me/theorems/89808928-065a-46e8-9eba-9728c6369879
-- title:
--   Locality: dai Li Atom Qubits upper eq half Open
-- statement:
--   The upper child rectangle is the complementary half-open slice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L399-L422
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L399-L422

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

theorem QEC.Locality.daiLiAtomQubits_upper_eq_halfOpen
    (embedding : UnitSeparatedEmbedding2D ι) (left right lower cut upper : ℝ)
    (hLowerCut : lower < cut) (hCutUpper : cut < upper) :
    daiLiAtomQubits embedding left right (cut, upper) =
      daiLiAtOrAboveHorizontalCut embedding (left, lower) (right, upper) cut := by sorry
