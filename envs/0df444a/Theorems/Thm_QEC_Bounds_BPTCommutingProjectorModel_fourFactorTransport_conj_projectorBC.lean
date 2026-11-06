-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorBC
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorBC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:59.243507+00:00
-- url     : https://prove2.me/theorems/1ddc821c-e514-4ed4-807c-db5b364b9f60
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj projector BC
-- statement:
--   The middle source product has the exact `BC` support equation on the common
--   four-factor transport.  This is the second overlapping-projector input for
--   the BV03 tensor-block theorem, not a substitute joint spectral decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2413-L2420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2413-L2420

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorBC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorBC region) =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by sorry
