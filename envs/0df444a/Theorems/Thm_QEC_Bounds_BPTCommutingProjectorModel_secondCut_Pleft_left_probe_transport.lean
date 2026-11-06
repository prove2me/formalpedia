-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_left_probe_transport
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_left_probe_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:43:29.918623+00:00
-- url     : https://prove2.me/theorems/16093c29-abf1-4fe4-8415-b570622819c5
-- title:
--   BPTCommuting Projector Model: second Cut Pleft left probe transport
-- statement:
--   The second-cut block transport sends the selected left probe to `X tensor 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftProbe.lean#L68-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/LeftProbe.lean#L68-L100

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Coordinates
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftProbe
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_left_probe_transport
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (H W0 : Submodule Complex (M.fourFactorB region))
    {n : Nat} [NeZero n]
    :
    let A := M.fourFactorA region
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (X : Semantics.Operator (Semantics.CompositeSystem A W0)),
      (isotypicSectorBlockTransportLeft A H W0 N CD U).conjOperator
          (overlapLiftLeft (C := CD)
            ((unitaryLTensor A U).symm.conjOperator
              (rightTensorExtensionAfterLeft A W0 N X))) =
        TensorProduct.map X (1 : Semantics.Operator (Semantics.CompositeSystem N CD)) := by sorry
