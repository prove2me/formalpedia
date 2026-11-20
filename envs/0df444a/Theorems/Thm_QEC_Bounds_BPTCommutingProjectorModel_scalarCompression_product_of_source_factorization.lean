-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_scalarCompression_product_of_source_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.scalarCompression_product_of_source_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:42:05.954424+00:00
-- url     : https://prove2.me/theorems/3efea7ca-a8a8-47c4-9405-c9119365a90c
-- title:
--   BPTCommuting Projector Model: scalar Compression product of source factorization
-- statement:
--   The source equation `Pi O_M1 O_M2 Pi = f(O_M1) Pi O_M2 Pi`, combined with
--   the #402 no-information consequence for `M2`, gives scalar compression of
--   every separated local product.  This is the semantic tail of the BPT union
--   argument; its factorization premise is discharged below from #388 data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/Core.lean#L133-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/Core.lean#L133-L176

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_SourceLift
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_Core
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

theorem QEC.Bounds.BPTCommutingProjectorModel.scalarCompression_product_of_source_factorization
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hright : M.RegionErasureRecoverable right)
    (hfactor : ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      ∃ coefficient : Complex,
        M.fullCodeProjector * (M.regionSubsystem left).extendLocalToRegister A *
            (M.regionSubsystem right).extendLocalToRegister B * M.fullCodeProjector =
          coefficient •
            (M.fullCodeProjector * (M.regionSubsystem right).extendLocalToRegister B *
              M.fullCodeProjector))
    (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
    (B : Semantics.Operator (M.regionSubsystem right).selectedSystem) :
    Semantics.QuditSubsystem.ScalarCompression M.codeSpace
      ((M.regionSubsystem left).extendLocalToRegister A *
        (M.regionSubsystem right).extendLocalToRegister B) := by sorry
