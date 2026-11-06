-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_exteriorLocal_exists
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_exteriorLocal_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:16.426869+00:00
-- url     : https://prove2.me/theorems/f9ea1280-3c87-44e1-88fa-8834828d08d6
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj exterior Local exists
-- statement:
--   Every operator supported in the actual source exterior has a concrete `D`
--   representative after the four-factor transport.  The representative is
--   obtained by explicit coordinate lift and relabeling, rather than by an
--   abstract support or factorization premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/FourFactor.lean#L122-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/FourFactor.lean#L122-L165

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1000000

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_exteriorLocal_exists
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    ∃ Z : Semantics.Operator (M.fourFactorD region),
      (M.fourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P) =
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
            (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by sorry
