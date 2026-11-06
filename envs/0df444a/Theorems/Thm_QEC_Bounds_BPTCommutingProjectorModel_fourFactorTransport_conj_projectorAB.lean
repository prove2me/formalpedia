-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorAB
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorAB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:27.84181+00:00
-- url     : https://prove2.me/theorems/b86ab7c2-c049-47ac-a9d1-502c3e9ab777
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj projector AB
-- statement:
--   The first source product has the exact `AB` support equation on the common
--   four-factor transport.  This realizes the `Pi_AB` side of both overlapping
--   commuting-projector cuts without replacing it by a global spectral sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2371-L2390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2371-L2390

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorAB
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorAB region) =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) := by sorry
