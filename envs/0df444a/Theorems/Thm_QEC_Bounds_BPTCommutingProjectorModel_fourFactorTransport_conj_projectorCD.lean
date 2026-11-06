-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorCD
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorCD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:16:31.292722+00:00
-- url     : https://prove2.me/theorems/a15c5fa4-b0e1-4a6d-a679-7abbb005017c
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj projector CD
-- statement:
--   The third source product has the exact `CD` support equation on the common
--   four-factor transport.  Together with the `AB` equation, this is the actual
--   overlapping-locality input to the BV03 interaction-algebra decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2397-L2406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2397-L2406

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorCD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorCD region) =
      M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by sorry
