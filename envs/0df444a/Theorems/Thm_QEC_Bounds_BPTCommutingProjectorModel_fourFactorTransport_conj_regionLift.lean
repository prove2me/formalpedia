-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_regionLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_regionLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:19.656181+00:00
-- url     : https://prove2.me/theorems/1ee1c771-bac0-4709-9f4a-45c2b5a51666
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj region Lift
-- statement:
--   An arbitrary operator supported on the physical region `M` becomes the
--   literal left `AB` lift in the four-factor coordinates.  This is the
--   locality transport used immediately below to carry hM no-information into
--   the second BV03 block, rather than only for the distinguished source
--   projector `Pi_AB`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Transport.lean#L30-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Transport.lean#L30-L54

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_RankOne
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Transport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_regionLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem region).selectedSystem) :
    (M.fourFactorTransport region).conjOperator
      ((M.regionSubsystem region).extendLocalToRegister P) =
      M.fourFactorExtendAB region
        (((M.regionSubsystem (M.interior region)).selectedFactorization
          (M.regionSubsystem region) (by
            intro site hsite
            exact (Finset.mem_sdiff.mp hsite).1)).conjOperator P) := by sorry
