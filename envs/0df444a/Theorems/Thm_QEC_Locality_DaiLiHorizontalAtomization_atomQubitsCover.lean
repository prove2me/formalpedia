-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_atomQubitsCover
-- name    : QEC.Locality.DaiLiHorizontalAtomization.atomQubitsCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:51:25.649659+00:00
-- url     : https://prove2.me/theorems/9b49ca29-5347-4c05-ad5a-cf2ac53cc797
-- title:
--   Dai Li Horizontal Atomization: atom Qubits Cover
-- statement:
--   An actual global-support-free atomization covers exactly its parent rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L527-L557
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L527-L557

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

theorem QEC.Locality.DaiLiHorizontalAtomization.atomQubitsCover
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (hEll : 0 < ell) :
    daiLiAtomQubitsCover embedding left right atoms =
      embedding.qubitsInRectangle (left, lower) (right, upper) := by sorry
