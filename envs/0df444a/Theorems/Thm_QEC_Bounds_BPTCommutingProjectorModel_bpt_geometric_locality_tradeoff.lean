-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_bpt_geometric_locality_tradeoff
-- name    : QEC.Bounds.BPTCommutingProjectorModel.bpt_geometric_locality_tradeoff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:31:24.045253+00:00
-- url     : https://prove2.me/theorems/22e55f30-b7fa-4440-bcf7-965cae3bbd0b
-- title:
--   BPTCommuting Projector Model: bpt geometric locality tradeoff
-- statement:
--   [BPT10, Main result].  For the actual finite open square-lattice
--   commuting-projector model, the source measurement/no-information distance
--   obeys the geometric locality tradeoff.
--
--   The coefficient `16384 * w^4 * log_2(Q)` is Lean-QEC's explicit witness for
--   BPT10's existential constant depending only on the projector range `w` and
--   the uniform local-dimension bound `Q`; BPT10 does not state `16384`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/GeometricTradeoff.lean#L33-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/GeometricTradeoff.lean#L33-L47

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Definitions.Def_QEC_Results_LocalityBounds_GeometricTradeoff
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped BigOperators
universe v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.bpt_geometric_locality_tradeoff
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance : Nat)
    (hDistance : Semantics.QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hdistance : 0 < distance)
    (hregular : L.lattice.rows = L.lattice.columns) :
    (parameter.encodedQubits : Real) * (distance : Real) ^ 2 <=
      (16384 : Real) * (M.interactionRange : Real) ^ 4 *
        Real.logb 2 (L.uniformDimensionBound : Real) * (L.lattice.siteCount : Real) := by sorry
