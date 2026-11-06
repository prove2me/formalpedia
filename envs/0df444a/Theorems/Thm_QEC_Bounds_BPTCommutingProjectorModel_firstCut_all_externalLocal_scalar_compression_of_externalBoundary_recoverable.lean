-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:59:20.709093+00:00
-- url     : https://prove2.me/theorems/150145e4-76fd-4b92-a011-18e88a4932b9
-- title:
--   BPTCommuting Projector Model: first Cut all external Local scalar compression of external Boundary recoverable
-- statement:
--   External-boundary recoverability makes every literal virtual `C` probe scalar
--   on the first-cut code lift.  The relation is obtained from the physical
--   external-boundary extension, then carried through the concrete first-cut
--   global coordinates.  It is the hC input for the residual `C'` no-cloning
--   factor, not merely the sector-measurement special case above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4272-L4334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L4272-L4334

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 2000000

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (E : Semantics.Operator (M.fourFactorC region)) :
    ∃ scalar : Complex,
      M.firstCutCodeLift region *
          overlapLiftLeft (C := M.fourFactorD region)
            (TensorProduct.map
              (1 : Semantics.Operator
                (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) E) *
          M.firstCutCodeLift region = scalar • M.firstCutCodeLift region := by sorry
