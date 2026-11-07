-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactor_codeProjector_eq_source_products
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactor_codeProjector_eq_source_products
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:47.917773+00:00
-- url     : https://prove2.me/theorems/2757fc4e-3670-4a49-8861-df10f04024f1
-- title:
--   BPTCommuting Projector Model: four Factor code Projector eq source products
-- statement:
--   The canonical source-coordinate transport carries the full BPT code projector
--   to the literal product of its three source-local factors on `A B C D`.  This
--   is the single recombination point between the concrete geometry/support work
--   and the two BV03 overlapping-projector decompositions: the first cut groups
--   `AB` with `BC`, and the second groups `BC` with `CD`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2674-L2705
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2674-L2705

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactor_codeProjector_eq_source_products
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator M.fullCodeProjector =
      (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
        M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region)) *
        M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by sorry
