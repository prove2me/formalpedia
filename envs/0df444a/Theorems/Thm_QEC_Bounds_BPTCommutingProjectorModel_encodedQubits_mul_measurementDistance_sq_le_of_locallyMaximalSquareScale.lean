-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_encodedQubits_mul_measurementDistance_sq_le_of_locallyMaximalSquareScale
-- name    : QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_mul_measurementDistance_sq_le_of_locallyMaximalSquareScale
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:29:26.826616+00:00
-- url     : https://prove2.me/theorems/6ba54ecc-79b6-425d-aa19-1815bfecc94e
-- title:
--   BPTCommuting Projector Model: encoded Qubits mul measurement Distance sq le of locally Maximal Square Scale
-- statement:
--   The exact finite BPT synthesis under the source maximal-square certificate.
--   The checkerboard cores have side `R - 2w`, while their recoverable envelopes
--   have side `R`; the resulting constant is explicit and depends only on the
--   local range upper bound and the local dimension upper bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L3000-L3088
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L3000-L3088

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_mul_measurementDistance_sq_le_of_locallyMaximalSquareScale
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance blockWidth margin envelopeWidth tileRows tileColumns : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hblockWidth : 0 < blockWidth) (hrange : M.interactionRange ≤ margin)
    (hseparationWidth : margin + margin ≤ blockWidth)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hmax : M.LocallyMaximalCorrectableSquareScale envelopeWidth)
    (hnonemptyA : (L.lattice.squarePartitionAComponents blockWidth margin).Nonempty)
    (hnonemptyB : (L.lattice.squarePartitionBComponents blockWidth margin).Nonempty) :
    (parameter.encodedQubits : Real) * (distance : Real) ^ 2 ≤
      (4096 : Real) * (margin : Real) ^ 4 *
        Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by sorry
